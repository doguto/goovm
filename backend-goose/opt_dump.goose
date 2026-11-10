// A text dump of the optimizer's output tables (GOOVM_OPT=dump, on stderr),
// for debugging: one line per instruction, `%N` = module-global
// instruction index in the output, `aN` argument, `#v:t` integer constant,
// `cN` other constant, `@name` global, `bN` local block.

let OPN = ["ret", "br", "condbr", "switch", "unreachable", "add", "sub", "mul", "sdiv", "udiv", "srem",
    "urem", "and", "or", "xor", "shl", "lshr", "ashr", "icmp", "select", "zext", "sext", "trunc", "ptrtoint",
    "inttoptr", "bitcast", "alloca", "load", "store", "gep", "call", "phi", "fadd", "fsub", "fmul", "fdiv", "fneg",
    "fcmp", "fpext", "fptrunc", "fptosi", "fptoui", "sitofp", "uitofp", "extractvalue", "insertvalue",
    "extractelt", "insertelt", "shuffle", "dynalloca", "stacksave", "stackrestore", "vastart", "memcpy", "memset",
    "ctlz", "cttz", "ctpop", "bswap", "bitreverse", "fshl", "fshr", "ovf", "scmp", "ucmp", "fabs", "copysign",
    "fsqrt", "isfpclass", "cmpxchg", "atomicrmw", "fence", "tlsaddr", "frameaddr", "retaddr", "sjlj_setjmp",
    "sjlj_longjmp", "trap", "debugtrap", "indirectbr", "blockaddr", "x86", "asm", "landingpad"];

fn dump_val(o: u8[>..]&, v: u32, fbase: u32) {
    let k = gir_kind(v);
    let i = gir_idx(v);
    if v == GIR_NONE { o.append("none"); return; }
    if k == GIR_V_INST { format(o, "%", i); return; }
    if k == GIR_V_ARG { format(o, "a", i); return; }
    if k == GIR_V_CONST {
        let C = x_consts[xb_c + i];
        if cls_of(C.ty) == C_INT && C.data == GIR_NONE { format(o, "#", sx(C.lo, bits_of(C.ty)), ":", C.ty); }
        else { format(o, "c", i, ":", C.ty); }
        return;
    }
    let G = M.globals[i];
    o.append("@");
    o.append(M.strtab[G.name..G.name + G.name_len]);
}

fn dump_module() {
    var o: u8[>..] = [];
    for F, fi in x_funcs[xb_f..] {
        let G = M.globals[F.global];
        format(o, "func ", fi, " @");
        o.append(M.strtab[G.name..G.name + G.name_len]);
        format(o, " flags=", F.flags, " insts=", F.n_inst, "\n");
        for b in 0..F.n_blocks {
            let B = x_blocks[xb_b + F.first_block + b];
            format(o, " b", b, ":\n");
            for gi in B.first_inst..B.first_inst + B.n_inst {
                let I = x_insts[xb_i + gi];
                format(o, "   %", gi, " = ");
                if I.op < GIR_NOPS { o.append(OPN[I.op]); } else { format(o, "op", I.op); }
                if I.sub != 0 { format(o, ".", I.sub); }
                format(o, " t", I.ty);
                if I.aux != 0 { format(o, "/", I.aux); }
                let m: u32 = if I.op < GIR_NOPS { OP_VAL[I.op] } else { 7 };
                o.append(" ");
                if m & OV_A != 0 { dump_val(o, I.a, F.first_inst); } else { format(o, I.a); }
                o.append(", ");
                if m & OV_B != 0 { dump_val(o, I.b, F.first_inst); } else { format(o, I.b); }
                o.append(", ");
                if m & OV_C != 0 { dump_val(o, I.c, F.first_inst); } else { format(o, I.c); }
                let op: u32 = I.op;
                if op == GIR_GEP {
                    format(o, " [off ", x_opnds[xb_o + I.b], ";");
                    for k in 0..I.c {
                        o.append(" ");
                        dump_val(o, x_opnds[xb_o + I.b + 2 + 2 * k], F.first_inst);
                        format(o, "*", x_opnds[xb_o + I.b + 3 + 2 * k]);
                    }
                    o.append("]");
                } else if op == GIR_CALL || op == GIR_PHI {
                    o.append(" [");
                    for k in 0..I.c {
                        o.append(" ");
                        dump_val(o, x_opnds[xb_o + I.b + 2 * k], F.first_inst);
                        format(o, "/", x_opnds[xb_o + I.b + 2 * k + 1]);
                    }
                    o.append("]");
                } else if op == GIR_SWITCH {
                    format(o, " [default b", x_opnds[xb_o + I.b]);
                    for k in 0..I.c {
                        o.append(" ");
                        dump_val(o, x_opnds[xb_o + I.b + 1 + 2 * k], F.first_inst);
                        format(o, "->b", x_opnds[xb_o + I.b + 2 + 2 * k]);
                    }
                    o.append("]");
                }
                o.append("\n");
            }
        }
        if o.len > 1 << 20 {
            write_stderr(o);
            o.clear();
        }
    }
    write_stderr(o);
}
