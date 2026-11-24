// Tiny stack VM for make.fun's tiny-stack-vm-01 bounty. Node 22, plain JS in a .ts file.
// Runs /input/<id>/program.bin (with input.bin) and writes /output/<id>/stdout.bin + exit.txt.
import { readdirSync, readFileSync, writeFileSync, mkdirSync, statSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR || '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR || '/output';
const STEP_MAX = 1000000, OUT_MAX = 65536, MEM_MAX = 256, CALL_MAX = 64;

// IMM[op] is the immediate's width; -1 marks a byte no opcode names (trap 5).
const IMM = new Int8Array(256).fill(-1);
// META[op*2] and META[op*2+1] are the values an opcode pops and pushes.
const META = new Int8Array(512);
const def = (ops, p, q) => { for (const o of ops) { IMM[o] = 0; META[o * 2] = p; META[o * 2 + 1] = q; } };

def([0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e,
  0x20, 0x21, 0x22], 2, 1);
def([0x17, 0x1b, 0x40], 1, 1);
def([0x03, 0x31, 0x32, 0x50, 0x51, 0x53], 1, 0);
def([0x41], 2, 0);
def([0x04], 1, 2);
def([0x05, 0x06], 2, 3);
def([0x07], 3, 3);
def([0x01, 0x02, 0x52], 0, 1);
def([0x00, 0x30, 0x34], 0, 0);
IMM[0x01] = 1; IMM[0x02] = 4; IMM[0x30] = 2; IMM[0x31] = 2; IMM[0x32] = 2; IMM[0x33] = 2;
META[0x33 * 2] = 0; META[0x33 * 2 + 1] = 0;

function runVm(prog, input) {
  const st = new Int32Array(MEM_MAX), mem = new Int32Array(MEM_MAX), cs = new Int32Array(CALL_MAX);
  const out = Buffer.allocUnsafe(OUT_MAX), dg = Buffer.allocUnsafe(12);
  const n = prog.length, il = input.length;
  let sp = 0, cp = 0, ip = 0, ii = 0, ol = 0, s = 0, code = 0, halt = false;

  while (!halt) {
    if (s >= STEP_MAX) { code = 10; break; }
    if (ip < 0 || ip >= n) { code = 9; break; }
    const op = prog[ip], w = IMM[op];
    if (w < 0) { code = 5; break; }
    if (ip + 1 + w > n) { code = 9; break; }
    const p = META[op * 2], q = META[op * 2 + 1];
    if (sp < p) { code = 2; break; }
    if (sp - p + q > MEM_MAX) { code = 3; break; }

    s++;
    const nx = ip + 1 + w;

    switch (op) {
      case 0x00: code = 0; halt = true; break;
      case 0x01: st[sp++] = (prog[ip + 1] << 24) >> 24; break;
      case 0x02: st[sp++] = prog[ip + 1] | (prog[ip + 2] << 8) | (prog[ip + 3] << 16) |
        (prog[ip + 4] << 24); break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const a = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = a; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: {
        const c = st[sp - 1], b = st[sp - 2];
        st[sp - 1] = st[sp - 3]; st[sp - 3] = b; st[sp - 2] = c; break;
      }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = st[--sp], a = st[sp - 1];
        if (b === 0 && op >= 0x13 && op <= 0x16) { code = 4; halt = true; break; }
        st[sp - 1] =
          op === 0x10 ? (a + b) | 0 :
          op === 0x11 ? (a - b) | 0 :
          op === 0x12 ? Math.imul(a, b) :
          op === 0x13 ? (a / b) | 0 :
          op === 0x14 ? (a % b) | 0 :
          op === 0x15 ? ((a >>> 0) / (b >>> 0)) | 0 :
          op === 0x16 ? ((a >>> 0) % (b >>> 0)) | 0 :
          op === 0x18 ? a & b :
          op === 0x19 ? a | b :
          op === 0x1a ? a ^ b :
          op === 0x1c ? a << (b & 31) :
          op === 0x1d ? a >> (b & 31) :
          op === 0x1e ? (a >>> (b & 31)) | 0 :
          op === 0x20 ? (a === b ? 1 : 0) :
          op === 0x21 ? (a < b ? 1 : 0) :
          (a >>> 0) < (b >>> 0) ? 1 : 0;
        break;
      }
      case 0x17: st[sp - 1] = (0 - st[sp - 1]) | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        let go = true;
        if (op !== 0x30) { const v = st[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
        ip = go ? nx + (((prog[ip + 1] | (prog[ip + 2] << 8)) << 16) >> 16) : nx;
        continue;
      }
      case 0x33:
        if (cp >= CALL_MAX) { code = 7; halt = true; break; }
        cs[cp++] = nx;
        ip = prog[ip + 1] | (prog[ip + 2] << 8);
        continue;
      case 0x34:
        if (cp === 0) { code = 8; halt = true; break; }
        ip = cs[--cp];
        continue;
      case 0x40: {
        const a = st[sp - 1];
        if (a < 0 || a >= MEM_MAX) { code = 6; halt = true; break; }
        st[sp - 1] = mem[a]; break;
      }
      case 0x41: {
        const a = st[--sp], v = st[sp - 1];
        if (a < 0 || a >= MEM_MAX) { code = 6; halt = true; break; }
        mem[a] = v; sp--; break;
      }
      case 0x50: {
        const v = st[--sp];
        let k = 12;
        if (v === 0) dg[--k] = 48;
        else {
          const neg = v < 0;
          let u = neg ? -v : v;
          while (u > 0) { dg[--k] = 48 + (u % 10); u = Math.floor(u / 10); }
          if (neg) dg[--k] = 45;
        }
        if (ol + 12 - k > OUT_MAX) { code = 11; halt = true; break; }
        dg.copy(out, ol, k);
        ol += 12 - k; break;
      }
      case 0x51: {
        const v = st[--sp];
        if (ol === OUT_MAX) { code = 11; halt = true; break; }
        out[ol++] = v & 255; break;
      }
      case 0x52: st[sp++] = ii < il ? input[ii++] : -1; break;
      case 0x53: code = st[--sp] & 255; halt = true; break;
    }
    ip = nx;
  }

  return { out: out.subarray(0, ol), code };
}

mkdirSync(OUT, { recursive: true });
for (const id of readdirSync(IN).sort()) {
  const dir = join(IN, id);
  let stt;
  try { stt = statSync(dir); } catch { continue; }
  if (!stt.isDirectory()) continue;
  const r = runVm(readFileSync(join(dir, 'program.bin')), readFileSync(join(dir, 'input.bin')));
  const od = join(OUT, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), r.out);
  writeFileSync(join(od, 'exit.txt'), String(r.code) + '\n');
}