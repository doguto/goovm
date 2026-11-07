# Runtime patches (milestone G1)

A Goose program built as a standalone executable carries the Goose runtime
verbatim: the generated C (`goosecc.c`) contains `runtime_impl.h` and the
other runtime sources between `/* ==== runtime_impl.h ==== */` markers.
`build.sh` applies the patches of this directory to that generated file
(`patch -p1`, the paths name the runtime's own sources) before compiling
it, so the Goose checkout itself stays untouched. A patch that no longer
applies stops the build with a message; `RUNTIME_PATCHES=0
frontend-goose/build.sh OUT` builds with the runtime as Goose ships it.

| file | what |
|---|---|
| `lazy-regions.patch` | data stack regions reserved together, made accessible on first touch |
| `hot-regions.txt` | the regions nearly every compile touches (by global name), placed first and made accessible at start-up |
| `hot_regions.py` | makes `hot-regions.txt` from a profiling build (`PROFILE_REGIONS=1`) over CTMark |

## Why

Every growable global array of a Goose program (`var a: T[>..] = []`) is a
*data stack*: a region of its own, reserved at start-up (256 MB of address
space plus a 1 MB guard gap, `mmap` + `mprotect`) and grown in place.
goosecc has 420 of them (the front end's tables, the lowering's, the
back-end's). Measured on this VM (Linux 6.18, `frontend-goose/` scratch
benchmarks, best of many runs):

| cost | per region |
|---|---:|
| reserve (`mmap` + `mprotect` of the gap) and tear down at exit | 1.36 µs |
| first touch of a region (fresh page-table pages) | 3.1 µs |
| SIGSEGV → handler → `mprotect` → retry (the lazy path) | 2.6–2.9 µs |
| one more page fault inside an enabled region | 0.73 µs |

With 420 regions the eager reservation alone was about 0.57 ms of a
1.19 ms compile of a one-line file, and every exit unmapped 840 VMAs.
(`MADV_GUARD_INSTALL` for the gaps was slower than `mprotect`; transparent
huge pages gave nothing measurable.)

## What `lazy-regions.patch` does

- `gs_rt_start` makes **one** `PROT_NONE` reservation with a slot per
  region main will register (the registry size is known from the program's
  stack registry), instead of one `mmap` per region.
- `gs_reserve_region` hands out the next slot without a system call. A
  slot's usable part becomes accessible on its first access: the runtime's
  SIGSEGV handler (which already tells stack overflows from other faults)
  sees an address inside a not-yet-enabled slot, `mprotect`s that slot's
  usable part read/write (halving down to 1 MB if the kernel refuses the
  whole), and returns, so the access is retried. The guard gap stays
  `PROT_NONE`: overflow detection is unchanged.
- **Hot regions** (`GS_HOT_REGIONS`, a list of registry indices that
  `build.sh` derives from `hot-regions.txt` and the generated C's region
  order, `$OUT/regions.txt`): they take the first slots, next to each other
  so that their first pages share page-table pages, and are enabled as
  they are reserved (cheaper than the fault). 146 of the 420 are hot.
- Teardown releases the one reservation.
- `PROFILE_REGIONS=1` builds print, at exit, the registry indices of the
  regions a run touched (`gs_lazy_profile`), which `hot_regions.py` counts.

Result: compiling a one-line file went from 1.19 ms to about 0.65 ms of
wall time (0.63 ms task-clock, `exec` and exit included); a CTMark build
(316 files) gained about 10% of its warm time. Start-up is now dominated
by `exec`, the dynamic loader-free musl start, and the first touches of
the hot regions.

## Correctness risks

- **Fault handler re-entrancy.** The lazy path runs inside SIGSEGV. It
  calls only `mprotect` (async-signal-safe) and touches only the patch's
  own arrays, which are allocated before any region is used. A fault in a
  slot that is already enabled, or outside the reservation, goes to the
  runtime's original handling (overflow report or the default action).
- **Signal masks and alternate stacks.** The handler runs on the runtime's
  alternate signal stack, as before. A program that blocks SIGSEGV, or
  installs its own handler, would break the lazy path; goosecc does
  neither.
- **Threads.** The registry counter is updated with the runtime's own
  discipline (regions are registered on the main thread before any
  thread starts in goosecc). A threaded Goose program registering regions
  concurrently would need the slot allocation to be atomic (`gs_lazy_used`
  is `volatile`, not atomic).
- **Debuggers and tools.** gdb stops at every first touch (SIGSEGV) unless
  told `handle SIGSEGV nostop noprint`; valgrind sees the faults too
  (it works, slowly). `RUNTIME_PATCHES=0` gives the eager runtime.
- **Overcommit.** One large `PROT_NONE` reservation is the same address
  space as before, in one VMA; with `vm.overcommit_memory=2` neither form
  commits memory until a slot is enabled.
- **Upgrades.** The patch is a diff against the runtime goosecc was built
  with; `build.sh` refuses to build if it stops applying, rather than
  building something half-patched.

## Proposal for the Goose authors

The patch is small (about 280 lines of C) and could live in the runtime
behind a switch:

1. **Reserve all of main's regions at once.** The registry already knows
   how many regions `main` will have; a single reservation with fixed-size
   slots removes one `mmap`/`mprotect` pair per global array at start-up
   and two VMAs per array at exit. This alone is the bulk of the gain for
   programs with many global arrays.
2. **Enable slots on first touch** in the existing SIGSEGV handler (it
   already distinguishes guard-gap hits). Unused arrays then cost nothing.
3. **Let the build name hot regions** (a list of registry indices, as here,
   or a per-array attribute such as `@hot`) so that arrays touched on every
   run are enabled eagerly and packed together.
4. Keep an opt-out (`GS_NO_LAZY_REGIONS`, as the patch has) for
   environments where SIGSEGV handling is unwelcome (debuggers, programs
   with their own handlers).

A cheaper first step, without fault handling: reserve all slots in one
`mmap` and `mprotect` each slot's usable part when it is registered. That
keeps one VMA for the reservation but still pays one `mprotect` per region
(about half of today's cost).
