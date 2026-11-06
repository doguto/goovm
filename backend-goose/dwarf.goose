// DWARF 5 debug information (placeholder).

var dbg_on = false;
var s_dbg: u8[>..] = [];

fn dbg_init() {
    dbg_on = false;
    s_dbg.clear();
}
fn dbg_make_sections() {}
fn dbg_keep_homes(fi: u32) {}
fn dbg_func_start(sp: u32) {}
fn dbg_block_start() {}
fn dbg_inst(d: u32) {}
fn dbg_block_end() {}
fn dbg_epilogue() {}
fn dbg_func_end(fi: u32, start: u32, prolen: u32, size: u32, sec: u32) {}
fn dbg_write() {}
