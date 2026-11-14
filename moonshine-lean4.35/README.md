# The moonshine part of LeanVOA on Lean v4.35, with AxiomMath's CFSG library

This folder is a separate Lake project. It contains the moonshine part of the LeanVOA library (the import closure of
`VOA.Moonshine`, 1,030 files ported from the Lean v4.30 library in the parent directory) plus one new file,
`VOA/Moonshine/MoonshineLRCFSGBridge.lean`. It depends on AxiomMath's Lean formalization of the classification of
finite simple groups, [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG), at commit
`5437cdc31389dd9aeaa5c2a9465a4e164f8dea33`.

- Toolchain: Lean `v4.35.0-rc3`, Mathlib commit `b63f6e8a68d220e3b3bc4f3792bb53650d375f24` (the pins of that CFSG
  commit).
- Module names are the same as in the v4.30 library (`VOA.…`).

## What it proves

In the v4.30 library, monstrous moonshine for AxiomMath's Monster `AutO` is proved given one named hypothesis,
`GmatEqAutO : Prop := Generated.Gmat = AutO`. Here that hypothesis is a theorem: it is AxiomMath's
`CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess`. So the following holds with no hypotheses
(`VOA/Moonshine/MoonshineLRCFSGBridge.lean`):

```lean
theorem monstrousMoonshine_unconditional :
    ∃ φ : AutO ≃* AutVnat,
      (∀ g : AutO, vnatWeightTwoRestrict (φ g) = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB)) ∧
        ConwayNortonVia (φ : AutO →* AutVnat)
```

There is a group isomorphism `φ` from AxiomMath's Monster `AutO` onto `Aut V♮`. For every `g`, `φ g` acts on the
Griess algebra `V♮₂ ≅ ℂ ⊗ SpaceB` as `g` does, and the McKay–Thompson series of `φ g` is the normalised Hauptmodul of
a genus-zero group containing some `Γ₀(N)`. The file also has `gmatEqAutO : GmatEqAutO`,
`monsterEquivAutVnat' : AutO ≃* AutVnat` and `monsterEquivAutVnat'_restrict`. All of them depend only on `propext`,
`Classical.choice` and `Quot.sound`.

## How AxiomMath's theorem applies to our definitions

- **Shared structures.** The Monster definitions in `VOA/Moonshine/MonsterGriess/` use AxiomMath's own structures
  `CFSG.Monster.Code.F4`, `CFSG.Monster.Spin.SpinCoord` and `CFSG.Monster.Code.Parker`, its Golay code
  `CFSG.Monster.Code.C` and its map `CFSG.Monster.SpinLattice.phi0`. Everything else is AxiomMath's text, renamed.
  So `Generated.Gmat` and `AutO` here are *definitionally* AxiomMath's `Gmat` and `AutO`.
- **Why sharing was needed.** In v1.05 the copies were textually identical but redeclared the structures. A Lean
  structure is a nominal type, so that was not enough.
- **The kernel step.** Lean's kernel accepts `gmat_eq_griess` as a proof of `GmatEqAutO` in milliseconds. The
  elaborator runs out of heartbeats unfolding the Griess product. So `gmatEqAutO` is added by a short `run_cmd` that
  passes this one declaration to the kernel (`addDecl`). The result is an ordinary kernel-checked theorem.

## Building

```sh
lake exe cache get        # Mathlib build cache
lake build                # VOA.Moonshine and the bridge, including AxiomMath's library from source
```

**Build cost.** AxiomMath publishes no build cache. `lake build VOA.Moonshine` alone needs only about 45 small
CFSG modules. The bridge needs the full proof of `gmat_eq_griess`: about 20,000 CFSG modules, many hours, and a lot
of memory.

**macOS (case-insensitive file systems).** The CFSG repository contains two pairs of data files whose names differ
only in case:
- `CFSG/Certificates/Kernel/BabyMonster/Max2/data/R4.bin` and `r4.bin`;
- `CFSG/Certificates/Kernel/BabyMonster/Fu/data/W.bin` and `w.bin`.

A macOS checkout keeps only one file of each pair. The modules that read them pin the size and hash of the file they
read:

| File | Read by |
|---|---|
| `r4.bin` | `Max2.Data0` |
| `R4.bin` | `Max2.Data2` |
| `W.bin` | `Fu.Data0` |
| `w.bin` | `Fu.Data5` |

Lake does not track these files, so put the right one in place before building each reader, for example with
`git -C .lake/packages/cfsg show HEAD:<path> > <path>`. `Fu.Data5` is not needed for `gmat_eq_griess`. Linux is not
affected.

## Checking

```sh
lake env lean -DmaxSynthPendingDepth=3 <file with `#print axioms VOA.Moonshine.ConwayNorton.monstrousMoonshine_unconditional`>
```

This prints `[propext, Classical.choice, Quot.sound]`.
