import Mathlib
import Actlib.Laplace.LogConvexityBound
import Actlib.Laplace.Reflection
import Actlib.Laplace.StandingData
import Actlib.Laplace.QuadraticInequalities
import Actlib.Laplace.StretchedExponential
import Actlib.Laplace.ComplexScaleGamma
import Actlib.Laplace.Integrand
import Actlib.Laplace.RayRepresentation
import Actlib.Laplace.Bounds
import Actlib.Laplace.ContourIntegral
import Actlib.Laplace.Fubini
import Actlib.Laplace.Rotation
import Actlib.Laplace.Plemelj
import Actlib.Laplace.MainTheorem

/-!
# Entry point

Formalization of `wright_laplace.tex`.

* The lemma `lem:gammabound` ("Log-convexity bound") of the source document is formalized in
  `RequestProject/LogConvexityBound.lean`; see
  `WrightLaplace.Gamma_mul_natCast_add_one_le_factorial_rpow` and the statements accompanying
  equation `eq:entire` there.
* The lemma `lem:reflection` ("Reflection with conventions") is formalized in
  `RequestProject/Reflection.lean`; see `WrightLaplace.one_div_Gamma_neg`.
* The standing data `θ` (equation `eq:theta`), `c₁`, `c₂` are set up in
  `RequestProject/StandingData.lean`.
* The lemma `lem:quad` ("Two quadratic inequalities") is formalized in
  `RequestProject/QuadraticInequalities.lean`; see the statements accompanying equations
  `eq:quad1` and `eq:quad2` there.
* The lemma `lem:stretched` ("A stretched-exponential integral") is formalized in
  `RequestProject/StretchedExponential.lean`; see
  `WrightLaplace.integral_exp_neg_mul_rpow` and `WrightLaplace.integrableOn_exp_neg_mul_rpow`.
* The lemma `lem:cgamma` ("Complex-scale Gamma integral") is formalized in
  `RequestProject/ComplexScaleGamma.lean`; see
  `WrightLaplace.integral_cpow_mul_cexp_neg_mul` and
  `WrightLaplace.integrableOn_cpow_mul_cexp_neg_mul`.
* The objects of the source needed from here on — the Wright function, the target integrand `g`
  of equation `eq:gdef`, the function `E` of equation `eq:E`, the ray integrand and the quantity
  `I(y)` of the lemma `lem:ray` — are defined in `RequestProject/Integrand.lean`.
* The lemma `lem:ray` ("Ray representation") is formalized in
  `RequestProject/RayRepresentation.lean`; see `WrightLaplace.integrableOn_rayIntegrand` and
  `WrightLaplace.g_eq_im_rayIntegral`.
* The corollary `cor:bounds` ("Bounds, continuity, integrability") is formalized in
  `RequestProject/Bounds.lean`; see `WrightLaplace.abs_g_le` (i), `WrightLaplace.continuousOn_g`
  (ii), and `WrightLaplace.integrableOn_g_mul_exp_neg` together with
  `WrightLaplace.integral_abs_g_mul_exp_neg_le` (iii).
* The contour integral `D(ψ)` of equation `eq:D`, and the facts making it well defined, are in
  `RequestProject/ContourIntegral.lean`; see `WrightLaplace.D`.
* The lemma `lem:fubini` ("Fubini") is formalized in `RequestProject/Fubini.lean`; see
  `WrightLaplace.integral_g_mul_exp_neg_eq_im_D`.
* The lemma `lem:rotation` ("Rotation invariance") is formalized in
  `RequestProject/Rotation.lean`; see `WrightLaplace.D_eq_of_mem_Ioc` and
  `WrightLaplace.D_eq_D_theta`.
* The lemma `lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") is formalized in
  `RequestProject/Plemelj.lean`; see `WrightLaplace.tendsto_im_D`, together with the three parts
  of its proof, `WrightLaplace.tendsto_Aterm` (a), `WrightLaplace.tendsto_Bterm` (b) and
  `WrightLaplace.tendsto_Cterm` (c).
* The theorem `thm:main` is formalized in `RequestProject/MainTheorem.lean`; see
  `WrightLaplace.integral_wright_positive_stable_unit` and
  `WrightLaplace.integrableOn_wright_positive_stable_unit`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxRecDepth 4000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false


set_option grind.warning false
