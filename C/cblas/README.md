# LAProof × GSL CBLAS

This directory connects **real-world BLAS code** to LAProof's verified floating-point
accuracy results.

## Scope

LAProof proves floating-point accuracy theorems (forward error bounds, etc.) about
*functional models* of basic linear-algebra programs (idealized list/matrix functions
that compute a result with a precisely specified sequence of IEEE-754 operations).
Those theorems live in [`accuracy_proofs/`](../../accuracy_proofs/), independent of any
particular C implementation.

The goal of this directory is the other half of the story: take a **real-world BLAS
implementation** and *prove* that the compiled C code implements one of those
functional models. We use the CBLAS layer of the **GNU Scientific Library (GSL)** as the
implementation under verification.

The pipeline for each routine is:

1. Take the GSL CBLAS source (under [`src/`](src/)) essentially verbatim, with only the
   minimal edits needed to run CompCert's `clightgen` on it.
2. Generate the Clight AST (a `*.v` file) with `clightgen`.
3. Define the **functional model** the C loop literally computes (in a `*_model.v` file),
   and prove it equals (up to `feq`) the LAProof accuracy model over which the error
   theorems are stated.
4. Write a VST **funspec** (in a `spec_*.v` file) whose postcondition relates the returned
   value to the LAProof model.
5. **Verify** the C function against that funspec with VST (in a `verif_*.v` file).

Once a routine is verified against a funspec phrased in terms of a LAProof model, the
corresponding accuracy theorem can be transferred to the value computed by the compiled C
code. The verification does *not* prove the accuracy theorem's preconditions on its own,
however. To apply the bound to the C result, one must separately establish that those
preconditions hold, and they fall into two kinds.

- **Already guaranteed by the funspec precondition.** Some of the theorem's preconditions
  are exactly things the funspec `PRE` already requires, so they hold for free (e.g. the
  equal-length precondition that the `cblas_ddot` funspec imposes on the input arrays).
- **Additional conditions one must discharge.** Other preconditions are not established by
  the funspec and must be proved on the side. The `cblas_ddot` and `cblas_dasum`
  specifications deliberately accept arbitrary floating-point inputs, including infinities
  and NaNs. Their accuracy theorems, however, require a no-overflow assumption that the
  accumulated model result is finite. Thus, a proof of the absence of overflow must be
  supplied separately for an accuracy bound to hold.

So the honest statement is: for inputs satisfying both the funspec `PRE` and the accuracy
theorem's own hypotheses, the bound holds of the C return value. In many cases (such as the
dot products and other reduction loops verified here) the one hypothesis the funspec does
not already supply is a *no-overflow* condition: that the accumulated result is finite.

For `cblas_ddot` that leftover precondition is exactly `Hfin`: the `dotprodF` result over
the two logical strided vectors must be finite. Requiring finite inputs would not establish
it anyway, since a sum of finite products can still round to an infinity. The corresponding
condition for `cblas_dasum` is that `sumF (map BABS (strided incX N X))` is finite.

The `feq` postcondition cooperates here: the funspec only guarantees that the C result is
`feq`-equal to the model value (equality up to `±0` and exceptional values), but once the result is finite,
`feq` upgrades to real-value equality, so the bound on the model value is literally a bound
on the compiled C output.

When stating the accuracy corollary for the C function, you choose how to carry `Hfin`:

- **Conditional corollary.** Keep `Hfin` as an explicit hypothesis. The bound then holds
  whenever the result is in fact finite, and whoever applies the corollary discharges
  `Hfin` for their particular inputs. (`Hfin` is a proof obligation about the result,
  not a runtime check in the C code.)
- **Unconditional corollary.** Strengthen the funspec `PRE` with magnitude/length bounds
  that imply finiteness. LAProof's [`finite_sum_from_bounded`](../../accuracy_proofs/sum_is_finite.v)
  and the `fun_bnd_le` lemmas turn such bounds into a proof of `Hfin`, so the corollary
  carries no extra hypothesis.

### GSL CBLAS upstream

- GSL project home: <https://www.gnu.org/software/gsl/>
- GSL source repository (Savannah git): <https://git.savannah.gnu.org/cgit/gsl.git>
- CBLAS directory in the repo: <https://git.savannah.gnu.org/cgit/gsl.git/tree/cblas>
- Shared BLAS kernels (`source_*.h`) used by the CBLAS routines: <https://git.savannah.gnu.org/cgit/gsl.git/tree/blas>

GSL is licensed under the GNU GPL; the files under [`src/`](src/) retain their upstream
copyright and license headers.

## What we've verified so far

| Operation | Precision | Function | Files |
|-----------|-----------|----------|-------|
| Dot product | double | `cblas_ddot` | [`src/ddot.c`](src/ddot.c), [`src/source_dot_r.h`](src/source_dot_r.h), [`include/cblas.h`](include/cblas.h), [`ddot.v`](ddot.v), [`ddot_model.v`](ddot_model.v), [`spec_ddot.v`](spec_ddot.v), [`verif_ddot.v`](verif_ddot.v) |
| Sum of absolute values | double | `cblas_dasum` | [`src/dasum.c`](src/dasum.c), [`src/source_asum_r.h`](src/source_asum_r.h), [`include/cblas.h`](include/cblas.h), [`dasum.v`](dasum.v), [`asum_model.v`](asum_model.v), [`spec_dasum.v`](spec_dasum.v), [`verif_dasum.v`](verif_dasum.v) |
| Scalar multiply (in place) | double | `cblas_dscal` | [`src/dscal.c`](src/dscal.c), [`src/source_scal_r.h`](src/source_scal_r.h), [`include/cblas.h`](include/cblas.h), [`dscal.v`](dscal.v), [`scal_model.v`](scal_model.v), [`spec_dscal.v`](spec_dscal.v), [`verif_dscal.v`](verif_dscal.v) |

**Scope and remaining limits:**

- `cblas_ddot` supports positive, negative, and zero strides for both input arrays. Its
  precondition ensures that every array access is in bounds and that computing and
  updating the C array indices cannot overflow a signed `int`. The result is `feq`-equal
  to `dotprodF` applied to the two logical strided vectors.
- `cblas_dasum` supports every signed-`int` stride. For a positive stride, the result is
  `feq`-equal to `sumF (map BABS (strided incX N X))`; for a nonpositive stride, the GSL
  kernel returns `+0.0` without accessing the input array. The `fabs` call is verified with
  VSTlib's `fabs_spec`.
- `cblas_dscal` is currently specified only for positive strides. It updates the input
  array in place and is verified exactly against `scal_strided incX N alpha X`, which
  scales the selected elements and leaves every unselected element unchanged.
- The proofs establish correspondence between the compiled C functions and the existing
  LAProof functional models. Applying `dotprod_forward_error` or `fSUM` additionally
  requires proving that the relevant model result is finite; this composition is not yet
  packaged as a checked C-level accuracy theorem.

## Conventions

This directory mirrors the model/spec/verif split used elsewhere in
[`C/`](../) (e.g. the sparse routines' `sparse_model.v` / `spec_sparse.v` /
`verif_sparse.v`): pure model functions and their lemmas in `*_model.v`, VST funspecs in
`spec_*.v`, and `semax_body` proofs in `verif_*.v`.
