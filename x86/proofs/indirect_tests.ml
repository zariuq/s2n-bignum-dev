(* Deterministic decoder and symbolic execution regressions for near indirect
   CALL and JMP. Run from the repository root, or load through simulator.ml. *)

needs "x86/proofs/base.ml";;

let indirect_contract_count = ref 0;;

(* The step leaves a no-base SIB address as word((0 + 8 * val a) + d), a
   RIP-relative one as word(val(word(pc + n)) + d) and [rsp-8] as
   word_add stackpointer (word (2 EXP 64 - 8)); put them in the plain forms
   used in the statements before using the assumptions. *)

let contract_norm_lemma = prove
 (`word(val(word(x + a):N word) + b):N word = word(x + (a + b))`,
  REWRITE_TAC[WORD_ADD; WORD_VAL; WORD_ADD_ASSOC]);;

let contract_neg8 = prove
 (`word_add x (word 18446744073709551608):int64 = word_sub x (word 8)`,
  REWRITE_TAC[WORD_RULE `word_sub x y = word_add x (word_neg y)`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let contract_tac execth =
  PURE_REWRITE_TAC[fst execth] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN X86_VSTEPS_TAC execth [1] THEN
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[ADD_CLAUSES; contract_norm_lemma;
                                        contract_neg8] THENC
                           NUM_REDUCE_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let run_contract name bytes stmt =
  let ibyteterm = mk_flist(map (fun b -> mk_comb(`word:num->byte`,
                                          mk_small_numeral b)) bytes) in
  let goal = subst [ibyteterm,`ibytes:byte list`] stmt in
  let execth = X86_MK_EXEC_RULE(REFL ibyteterm) in
  let th = prove(goal,contract_tac execth) in
  if hyp th <> [] then failwith ("indirect contract has hypotheses: " ^ name);
  incr indirect_contract_count;;

(* A near call: the target from register r, pushed return address pc+n *)

let call_reg_stmt reg n = subst [reg,`REG:(x86state,int64)component`;
                                 mk_small_numeral n,`n:num`]
 `!pc a stackpointer e.
    nonoverlapping (word pc,LENGTH ibytes) (word_sub stackpointer (word 8),8)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) ibytes /\
              read RIP s = word pc /\ read REG s = a /\ read RSP s = stackpointer /\
              read events s = e)
         (\s. read RIP s = a /\ read RSP s = word_sub stackpointer (word 8) /\
              read (memory :> bytes64 (word_sub stackpointer (word 8))) s = word(pc + n) /\
              read events s =
              CONS (EventStore (word_sub stackpointer (word 8),8))
                   (CONS (EventJump (word(pc + n),a)) e))
         (MAYCHANGE [RIP; RSP] ,,
          MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 8))] ,,
          MAYCHANGE [events])`;;

let () = run_contract "call rax (FF D0)" [0xff; 0xd0] (call_reg_stmt `RAX` 2);;
let () = run_contract "call r15 (41 FF D7)" [0x41; 0xff; 0xd7]
           (call_reg_stmt `R15` 3);;
let () = run_contract "call rax, REX.W (48 FF D0)" [0x48; 0xff; 0xd0]
           (call_reg_stmt `RAX` 3);;

(* call rsp: the target is RSP before the push *)

let () = run_contract "call rsp (FF D4)" [0xff; 0xd4]
 `!pc stackpointer e.
    nonoverlapping (word pc,LENGTH ibytes) (word_sub stackpointer (word 8),8)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) ibytes /\
              read RIP s = word pc /\ read RSP s = stackpointer /\ read events s = e)
         (\s. read RIP s = stackpointer /\ read RSP s = word_sub stackpointer (word 8) /\
              read (memory :> bytes64 (word_sub stackpointer (word 8))) s = word(pc + 2) /\
              read events s =
              CONS (EventStore (word_sub stackpointer (word 8),8))
                   (CONS (EventJump (word(pc + 2),stackpointer)) e))
         (MAYCHANGE [RIP; RSP] ,,
          MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 8))] ,,
          MAYCHANGE [events])`;;

(* call [rsp]: an 8-byte load from the old RSP, then the push *)

let () = run_contract "call [rsp] (FF 14 24)" [0xff; 0x14; 0x24]
 `!pc t stackpointer e.
    nonoverlapping (word pc,LENGTH ibytes) (word_sub stackpointer (word 8),8)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) ibytes /\
              read RIP s = word pc /\ read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = t /\ read events s = e)
         (\s. read RIP s = t /\ read RSP s = word_sub stackpointer (word 8) /\
              read (memory :> bytes64 (word_sub stackpointer (word 8))) s = word(pc + 3) /\
              read events s =
              CONS (EventStore (word_sub stackpointer (word 8),8))
                   (CONS (EventJump (word(pc + 3),t))
                         (CONS (EventLoad (stackpointer,8)) e)))
         (MAYCHANGE [RIP; RSP] ,,
          MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 8))] ,,
          MAYCHANGE [events])`;;

(* call [rsp-8]: the target is read from the slot that the push then
   overwrites, so the target is the old contents *)

let () = run_contract "call [rsp-8] (FF 54 24 F8)" [0xff; 0x54; 0x24; 0xf8]
 `!pc t stackpointer e.
    nonoverlapping (word pc,LENGTH ibytes) (word_sub stackpointer (word 8),8)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) ibytes /\
              read RIP s = word pc /\ read RSP s = stackpointer /\
              read (memory :> bytes64 (word_sub stackpointer (word 8))) s = t /\
              read events s = e)
         (\s. read RIP s = t /\ read RSP s = word_sub stackpointer (word 8) /\
              read (memory :> bytes64 (word_sub stackpointer (word 8))) s = word(pc + 4) /\
              read events s =
              CONS (EventStore (word_sub stackpointer (word 8),8))
                   (CONS (EventJump (word(pc + 4),t))
                         (CONS (EventLoad (word_sub stackpointer (word 8),8)) e)))
         (MAYCHANGE [RIP; RSP] ,,
          MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 8))] ,,
          MAYCHANGE [events])`;;

(* call [rip+0x100]: the target is the value in the slot, not RIP plus it *)

let () = run_contract "call [rip+0x100] (FF 15 ...)"
  [0xff; 0x15; 0x00; 0x01; 0x00; 0x00]
 `!pc t stackpointer e.
    nonoverlapping (word pc,LENGTH ibytes) (word_sub stackpointer (word 8),8)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) ibytes /\
              read RIP s = word pc /\ read RSP s = stackpointer /\
              read (memory :> bytes64 (word(pc + 262))) s = t /\
              read events s = e)
         (\s. read RIP s = t /\ read RSP s = word_sub stackpointer (word 8) /\
              read (memory :> bytes64 (word_sub stackpointer (word 8))) s = word(pc + 6) /\
              read events s =
              CONS (EventStore (word_sub stackpointer (word 8),8))
                   (CONS (EventJump (word(pc + 6),t))
                         (CONS (EventLoad (word(pc + 262),8)) e)))
         (MAYCHANGE [RIP; RSP] ,,
          MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 8))] ,,
          MAYCHANGE [events])`;;

(* A near jump: only RIP and the events change *)

let jmp_reg_stmt reg n = subst [reg,`REG:(x86state,int64)component`;
                                mk_small_numeral n,`n:num`]
 `!pc a e.
    ensures x86
     (\s. bytes_loaded s (word pc) ibytes /\
          read RIP s = word pc /\ read REG s = a /\ read events s = e)
     (\s. read RIP s = a /\
          read events s = CONS (EventJump (word(pc + n),a)) e)
     (MAYCHANGE [RIP] ,, MAYCHANGE [events])`;;

let () = run_contract "jmp rax (FF E0)" [0xff; 0xe0] (jmp_reg_stmt `RAX` 2);;
let () = run_contract "jmp r11 (41 FF E3)" [0x41; 0xff; 0xe3]
           (jmp_reg_stmt `R11` 3);;
let () = run_contract "jmp r15 (41 FF E7)" [0x41; 0xff; 0xe7]
           (jmp_reg_stmt `R15` 3);;
let () = run_contract "jmp rsp (FF E4)" [0xff; 0xe4] (jmp_reg_stmt `RSP` 2);;

let () = run_contract "jmp [rsp] (FF 24 24)" [0xff; 0x24; 0x24]
 `!pc t stackpointer e.
    ensures x86
     (\s. bytes_loaded s (word pc) ibytes /\
          read RIP s = word pc /\ read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = t /\ read events s = e)
     (\s. read RIP s = t /\
          read events s = CONS (EventJump (word(pc + 3),t))
                               (CONS (EventLoad (stackpointer,8)) e))
     (MAYCHANGE [RIP] ,, MAYCHANGE [events])`;;

let () = run_contract "jmp [rax*8+0x1234] (FF 24 C5 ...)"
  [0xff; 0x24; 0xc5; 0x34; 0x12; 0x00; 0x00]
 `!pc a t e.
    ensures x86
     (\s. bytes_loaded s (word pc) ibytes /\
          read RIP s = word pc /\ read RAX s = a /\
          read (memory :> bytes64 (word(8 * val a + 4660))) s = t /\
          read events s = e)
     (\s. read RIP s = t /\
          read events s = CONS (EventJump (word(pc + 7),t))
                               (CONS (EventLoad (word(8 * val a + 4660),8)) e))
     (MAYCHANGE [RIP] ,, MAYCHANGE [events])`;;

let () = run_contract "jmp [rip+0x100] (FF 25 ...)"
  [0xff; 0x25; 0x00; 0x01; 0x00; 0x00]
 `!pc t e.
    ensures x86
     (\s. bytes_loaded s (word pc) ibytes /\
          read RIP s = word pc /\
          read (memory :> bytes64 (word(pc + 262))) s = t /\
          read events s = e)
     (\s. read RIP s = t /\
          read events s = CONS (EventJump (word(pc + 6),t))
                               (CONS (EventLoad (word(pc + 262),8)) e))
     (MAYCHANGE [RIP] ,, MAYCHANGE [events])`;;

type indirect_decode_expectation = Exp of string | Rej;;

let indirect_decode_cases = [
  (* positive: calls *)
  [0xff; 0xd0], Exp "CALL_INDIRECT (%rax)";
  [0x41; 0xff; 0xd7], Exp "CALL_INDIRECT (%r15)";
  [0x48; 0xff; 0xd0], Exp "CALL_INDIRECT (%rax)";
  [0x49; 0xff; 0xd7], Exp "CALL_INDIRECT (%r15)";
  [0x44; 0xff; 0xd0], Exp "CALL_INDIRECT (%rax)";
  [0x42; 0xff; 0xd0], Exp "CALL_INDIRECT (%rax)";
  [0xff; 0xd4], Exp "CALL_INDIRECT (%rsp)";
  [0xff; 0x15; 0x78; 0x56; 0x34; 0x12],
    Exp "CALL_INDIRECT (Memop Quadword (Riprel (word 305419896)))";
  [0xff; 0x15; 0xf8; 0xff; 0xff; 0xff],
    Exp "CALL_INDIRECT (Memop Quadword (Riprel (word 18446744073709551608)))";
  [0xff; 0x14; 0x24], Exp "CALL_INDIRECT (Memop Quadword (%% (rsp,0)))";
  [0xff; 0x54; 0x24; 0xf8],
    Exp "CALL_INDIRECT (Memop Quadword (%% (rsp,18446744073709551608)))";
  [0x41; 0xff; 0x14; 0x24], Exp "CALL_INDIRECT (Memop Quadword (%% (r12,0)))";
  [0xff; 0x54; 0x8b; 0x10],
    Exp "CALL_INDIRECT (Memop Quadword (%%%% (rbx,2,rcx,&16)))";
  [0xff; 0x14; 0xc5; 0x34; 0x12; 0x00; 0x00],
    Exp "CALL_INDIRECT (Memop Quadword (Bsid NONE (SOME rax) (word 3) (word 4660)))";
  (* positive: jumps *)
  [0xff; 0xe0], Exp "JMP_INDIRECT (%rax)";
  [0x41; 0xff; 0xe3], Exp "JMP_INDIRECT (%r11)";
  [0x41; 0xff; 0xe7], Exp "JMP_INDIRECT (%r15)";
  [0x48; 0xff; 0xe0], Exp "JMP_INDIRECT (%rax)";
  [0xff; 0xe4], Exp "JMP_INDIRECT (%rsp)";
  [0xff; 0x25; 0x78; 0x56; 0x34; 0x12],
    Exp "JMP_INDIRECT (Memop Quadword (Riprel (word 305419896)))";
  [0xff; 0x24; 0xc5; 0x34; 0x12; 0x00; 0x00],
    Exp "JMP_INDIRECT (Memop Quadword (Bsid NONE (SOME rax) (word 3) (word 4660)))";
  [0xff; 0x24; 0xc5; 0xf0; 0xff; 0xff; 0xff],
    Exp "JMP_INDIRECT (Memop Quadword (Bsid NONE (SOME rax) (word 3) (word 18446744073709551600)))";
  [0xff; 0x24; 0x24], Exp "JMP_INDIRECT (Memop Quadword (%% (rsp,0)))";
  [0xff; 0x64; 0x24; 0xf8],
    Exp "JMP_INDIRECT (Memop Quadword (%% (rsp,18446744073709551608)))";
  [0x48; 0xff; 0x64; 0x8b; 0x10],
    Exp "JMP_INDIRECT (Memop Quadword (%%%% (rbx,2,rcx,&16)))";
  (* negative: far forms, PUSH r/m, /7, FE /2 and /4 *)
  [0xff; 0x18], Rej; [0xff; 0xd8], Rej; [0x48; 0xff; 0x18], Rej;
  [0xff; 0x28], Rej; [0xff; 0xe8], Rej; [0x48; 0xff; 0x28], Rej;
  [0xff; 0x30], Rej; [0xff; 0xf0], Rej; [0x41; 0xff; 0xf7], Rej;
  [0xff; 0x38], Rej; [0xff; 0xf8], Rej;
  [0x8f; 0x00], Rej; [0x8f; 0xc0], Rej;
  [0xfe; 0xd0], Rej; [0xfe; 0x10], Rej; [0xfe; 0xe0], Rej; [0xfe; 0x20], Rej;
  (* negative: prefixes on the new forms *)
  [0x66; 0xff; 0xd0], Rej; [0x66; 0xff; 0xe0], Rej;
  [0x66; 0x48; 0xff; 0xd0], Rej; [0x66; 0xff; 0x14; 0x24], Rej;
  [0x3e; 0xff; 0xd0], Rej; [0x3e; 0xff; 0xe0], Rej;
  [0x3e; 0xff; 0x24; 0xc5; 0x34; 0x12; 0x00; 0x00], Rej;
  [0xf2; 0xff; 0xd0], Rej; [0xf2; 0xff; 0xe0], Rej; [0xf3; 0xff; 0xd0], Rej;
  [0x2e; 0xff; 0xd0], Rej; [0x26; 0xff; 0xe0], Rej; [0x36; 0xff; 0xd0], Rej;
  [0x67; 0xff; 0xd0], Rej; [0x67; 0xff; 0x10], Rej;
  [0xf0; 0xff; 0xd0], Rej; [0xf0; 0xff; 0x10], Rej;
  (* unchanged neighbours (compared between unpatched and patched) *)
  [0xff; 0xc0], Exp "INC (%eax)"; [0x48; 0xff; 0xc0], Exp "INC (%rax)";
  [0x41; 0xff; 0xc0], Exp "INC (%r8d)"; [0x49; 0xff; 0xc8], Exp "DEC (%r8)";
  [0xfe; 0xc0], Exp "INC (%al)"; [0xfe; 0xc4], Exp "INC (%ah)";
  [0x40; 0xfe; 0xc4], Exp "INC (%spl)";
  [0xff; 0x00], Exp "INC (Memop Doubleword (%% (rax,0)))";
  [0x48; 0xff; 0x08], Exp "DEC (Memop Quadword (%% (rax,0)))";
  [0xfe; 0x08], Exp "DEC (Memop Byte (%% (rax,0)))";
  [0x66; 0xff; 0xc0], Rej;
  [0xf7; 0xe2], Exp "MUL2 (%edx,%eax) (%edx)";
  [0x48; 0xf7; 0xe2], Exp "MUL2 (%rdx,%rax) (%rdx)";
  [0xf7; 0xd8], Exp "NEG (%eax)";
  [0x48; 0xf7; 0x1c; 0x24], Exp "NEG (Memop Quadword (%% (rsp,0)))";
  [0xf6; 0xc3; 0x15], Exp "TEST (%bl) (Imm8 (word 21))"];;

(* DECODE_CONV reports unsupported encodings through these failures.
   An unexpected conversion error must fail the test, not count as rejection. *)

let indirect_decode bytes =
  let term = mk_comb(`decode`,mk_flist(map (fun byte ->
    mk_comb(`word:num->byte`,mk_small_numeral byte)) bytes)) in
  try Some(DECODE_CONV term) with Failure message when
    mem message ["eval_opt got NONE";
      "evaluate 'if has_pfxs pfxs then NONE...' failed";
      "inst_bitpat_numeral: number does not match pattern"] -> None;;

let () =
  List.iter (fun (bytes,expected) ->
    let decoded = indirect_decode bytes in
    match decoded,expected with
    | Some theorem,Exp instruction ->
        let actual,remaining = dest_pair(rand(rhs(concl theorem))) in
        if hyp theorem <> [] || dest_list remaining <> [] ||
           not(aconv actual (parse_term instruction)) then
          failwith "indirect decoder regression"
    | None,Rej -> ()
    | _ -> failwith "indirect decoder acceptance regression")
    indirect_decode_cases;
  if !indirect_contract_count <> 14 then
    failwith "indirect contract coverage";
  check_axioms();
  Printf.printf "Indirect model regressions: %d decodings, %d contracts passed\n%!"
    (List.length indirect_decode_cases) !indirect_contract_count;;
