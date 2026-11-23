#!/usr/bin/env python3
"""Pruebas numéricas, cotas y aserciones para los 7 Problemas del Milenio (modelos)."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass


# =====================================================================
# 1. P vs NP: Semántica de fórmulas booleanas y cotas de crecimiento
# =====================================================================

@dataclass(frozen=True)
class Var:
    idx: int


@dataclass(frozen=True)
class Not:
    child: object


@dataclass(frozen=True)
class And:
    left: object
    right: object


@dataclass(frozen=True)
class Or:
    left: object
    right: object


def eval_formula(formula: object, assign: dict[int, bool]) -> bool:
    if isinstance(formula, Var):
        return bool(assign.get(formula.idx, False))
    if isinstance(formula, Not):
        return not eval_formula(formula.child, assign)
    if isinstance(formula, And):
        return eval_formula(formula.left, assign) and eval_formula(formula.right, assign)
    if isinstance(formula, Or):
        return eval_formula(formula.left, assign) or eval_formula(formula.right, assign)
    raise TypeError(f"Nodo de fórmula no soportado: {type(formula)}")


def is_satisfiable(formula: object, num_vars: int) -> tuple[bool, dict[int, bool] | None]:
    for bits in itertools.product([False, True], repeat=num_vars):
        env = {i: bits[i] for i in range(num_vars)}
        if eval_formula(formula, env):
            return True, env
    return False, None


def run_p_vs_np_checks(max_n: int = 5) -> dict:
    f_unsat = And(Var(0), Not(Var(0)))
    f_sat_3cnf = And(Or(Var(0), Var(1)), Or(Not(Var(0)), Var(2)))
    f_xor_3 = And(
        Or(Var(0), Var(1)),
        And(Not(And(Var(0), Var(1))), Or(Var(1), Var(2))),
    )

    sat_cases = {
        "unsat_contradiction_x0_and_not_x0": is_satisfiable(f_unsat, 1)[0],
        "sat_2clauses_3vars": is_satisfiable(f_sat_3cnf, 3)[0],
        "sat_xor_chain_3vars": is_satisfiable(f_xor_3, 3)[0],
    }

    quad_n10 = 3 * (10 ** 2) + 5
    quad_bound_ok = all(3 * (n ** 2) + 5 <= 305 for n in range(11))

    growth_table = []
    crossover_n = None
    for n in range(1, max_n + 9):
        exp_space = 2 ** n
        poly_bound = 2 * (n ** 3) + 2
        if crossover_n is None and exp_space > poly_bound:
            crossover_n = n
        if n <= max_n or n in (8, 10, 12):
            growth_table.append(
                {
                    "n": n,
                    "two_pow_n": exp_space,
                    "poly_2n3_plus_2": poly_bound,
                    "exp_gt_poly": exp_space > poly_bound,
                }
            )

    assert sat_cases["unsat_contradiction_x0_and_not_x0"] is False, "La contradicción debe ser UNSAT."
    assert sat_cases["sat_2clauses_3vars"] is True, "f_sat_3cnf debe ser SAT."
    assert sat_cases["sat_xor_chain_3vars"] is True, "f_xor_3 debe ser SAT."
    assert quad_n10 == 305 and quad_bound_ok is True, "Falla la cota cuadrática para n <= 10."
    assert crossover_n == 12, f"Se esperaba cruce en n=12, obtenido n={crossover_n}."

    return {
        "sat_cases": sat_cases,
        "quadratic_cost_n10": quad_n10,
        "quadratic_bound_le_305_for_n_le_10": quad_bound_ok,
        "crossover_n_2pow_n_gt_2n3_plus_2": crossover_n,
        "growth_samples": growth_table,
    }


# =====================================================================
# 2. Navier-Stokes (modelo reducido 1D): Disipación y decaimiento de E(t)
# =====================================================================

def simulate_dissipative_energy(
    e0: float = 1.0,
    nu: float = 0.05,
    dt: float = 0.02,
    steps: int = 50,
    k_mode: float = 1.0,
) -> dict:
    if nu <= 0:
        raise ValueError("La viscosidad nu debe ser estrictamente positiva.")
    if dt < 0 or steps < 0:
        raise ValueError("dt y steps no pueden ser negativos.")

    factor = math.exp(-2.0 * nu * (k_mode ** 2) * dt)
    energies = [float(e0)]
    for _ in range(steps):
        energies.append(energies[-1] * factor)

    non_negative = all(e >= 0.0 for e in energies)
    monotone_non_increasing = all(
        energies[i + 1] <= energies[i] + 1e-15 for i in range(len(energies) - 1)
    )
    total_decay = energies[0] - energies[-1]

    assert non_negative is True, "La energía discreta debe mantenerse >= 0."
    assert monotone_non_increasing is True, "La energía debe ser monótona no creciente."
    assert total_decay >= -1e-15, "La disipación total no puede ser negativa."

    return {
        "e0": energies[0],
        "e_final": energies[-1],
        "total_energy_dissipated": total_decay,
        "step_factor": factor,
        "non_negative": non_negative,
        "monotone_non_increasing": monotone_non_increasing,
        "below_0_2_after_steps": energies[-1] < 0.2,
    }


# =====================================================================
# 3. Birch & Swinnerton-Dyer (BSD): Conteo sobre F_p y cota de Hasse
# =====================================================================

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def count_elliptic_points_mod_p(a: int, b: int, p: int) -> int:
    if not is_prime(p):
        raise ValueError(f"p={p} no es primo.")
    disc = (-16 * (4 * (a ** 3) + 27 * (b ** 2))) % p
    if disc == 0:
        raise ValueError("La curva es singular sobre F_p (discriminante 0 mod p).")

    rhs_counts = [0] * p
    for x in range(p):
        val = (x ** 3 + a * x + b) % p
        rhs_counts[val] += 1

    lhs_counts = [0] * p
    for y in range(p):
        lhs_counts[(y * y) % p] += 1

    affine_pts = sum(lhs_counts[v] * rhs_counts[v] for v in range(p))
    return 1 + affine_pts


def evaluate_single_curve(a: int, b: int, primes: list[int]) -> dict:
    rows = []
    all_within_hasse = True
    for p in primes:
        cnt = count_elliptic_points_mod_p(a, b, p)
        trace_ap = (p + 1) - cnt
        bound = 2.0 * math.sqrt(p)
        in_hasse = abs(trace_ap) <= bound + 1e-12
        if not in_hasse:
            all_within_hasse = False
        rows.append(
            {
                "p": p,
                "points_Fp": cnt,
                "a_p": trace_ap,
                "hasse_bound_2sqrt_p": round(bound, 4),
                "within_hasse": in_hasse,
            }
        )

    known_int_pts = [
        (x, y)
        for x in range(-5, 6)
        for y in range(-10, 11)
        if y * y == x ** 3 + a * x + b
    ]

    assert all_within_hasse is True, f"Cota de Hasse violada en y^2 = x^3 + {a}x + {b}."

    return {
        "curve": f"y^2 = x^3 + ({a})*x + ({b})",
        "known_small_integer_points": known_int_pts,
        "all_primes_within_hasse": all_within_hasse,
        "mod_p_samples": rows,
    }


def run_bsd_checks(a: int = -1, b: int = 0, primes: list[int] | None = None) -> dict:
    if primes is None:
        primes = [3, 5, 7, 11, 13, 17, 19, 23]

    primary = evaluate_single_curve(a, b, primes)
    secondary = evaluate_single_curve(0, 1, [5, 7, 11, 13, 17, 19])

    return {
        "primary_curve": primary,
        "secondary_curve_y2_eq_x3_plus_1": secondary,
        "all_curves_within_hasse": (
            primary["all_primes_within_hasse"] and secondary["all_primes_within_hasse"]
        ),
    }


# =====================================================================
# 4. Hipótesis de Riemann: Eta de Dirichlet y simetría conjugada
# =====================================================================

def dirichlet_eta(s: complex, terms: int = 4000) -> complex:
    acc = 0.0 + 0.0j
    sign = 1.0
    for n in range(1, terms + 1):
        acc += sign / (n ** s)
        sign = -sign
    return acc


def eta_to_zeta(s: complex, terms: int = 4000) -> complex:
    denom = 1.0 - (2.0 ** (1.0 - s))
    if abs(denom) < 1e-15:
        raise ValueError("Denominador cercano a cero en la relación eta -> zeta.")
    return dirichlet_eta(s, terms=terms) / denom


def run_riemann_checks(terms: int = 4000) -> dict:
    s_real = 2.0 + 0.0j
    zeta_2_est = eta_to_zeta(s_real, terms=terms)
    zeta_2_exact = (math.pi ** 2) / 6.0
    err_zeta_2 = abs(zeta_2_est.real - zeta_2_exact)

    probe_heights = [5.0, 14.1347251417, 21.0220396388, 25.0108575801]
    critical_probes = []
    for t_val in probe_heights:
        s_pt = complex(0.5, t_val)
        val_eta = dirichlet_eta(s_pt, terms=terms)
        critical_probes.append(
            {
                "s": f"0.5+{t_val}j",
                "eta_abs": round(abs(val_eta), 6),
            }
        )

    s_sample = complex(0.75, 5.0)
    eta_s = dirichlet_eta(s_sample, terms=terms)
    eta_conj = dirichlet_eta(s_sample.conjugate(), terms=terms)
    conj_diff = abs(eta_conj - eta_s.conjugate())

    assert err_zeta_2 < 1e-6, f"Error en zeta(2) demasiado alto: {err_zeta_2}"
    assert conj_diff < 1e-9, f"Simetría conjugada fuera de tolerancia: {conj_diff}"

    return {
        "terms_used": terms,
        "zeta_2_est": round(zeta_2_est.real, 8),
        "zeta_2_exact": round(zeta_2_exact, 8),
        "zeta_2_abs_error": err_zeta_2,
        "critical_line_probes": critical_probes,
        "conjugate_symmetry_diff": conj_diff,
        "conjugate_symmetry_ok": conj_diff < 1e-9,
    }


# =====================================================================
# 5. Yang-Mills, Hodge y Poincaré: Modelos discretos y consistencia
# =====================================================================

def run_yang_mills_hodge_poincare_checks(ring_n: int = 8) -> dict:
    if ring_n < 3:
        raise ValueError("ring_n debe ser >= 3 para brecha espectral positiva.")
    gap_lambda_1 = 2.0 - 2.0 * math.cos(2.0 * math.pi / ring_n)
    plaquette_vac = 1.0 - math.cos(0.0)
    plaquette_pert = 1.0 - math.cos(0.2)

    h_k3 = {
        (0, 0): 1, (1, 0): 0, (0, 1): 0,
        (2, 0): 1, (1, 1): 20, (0, 2): 1,
        (2, 1): 0, (1, 2): 0, (2, 2): 1,
    }
    sym_pq_ok = all(h_k3[(p, q)] == h_k3[(q, p)] for p, q in h_k3)
    chi_k3 = sum(((-1) ** (p + q)) * val for (p, q), val in h_k3.items())

    solids = [
        {"name": "tetraedro", "V": 4, "E": 6, "F": 4, "genus": 0},
        {"name": "cubo", "V": 8, "E": 12, "F": 6, "genus": 0},
        {"name": "toro_malla_3x3", "V": 9, "E": 18, "F": 9, "genus": 1},
    ]
    euler_checks = []
    for s in solids:
        chi_vf = s["V"] - s["E"] + s["F"]
        chi_genus = 2 - 2 * s["genus"]
        euler_checks.append(
            {
                "name": s["name"],
                "chi_V_E_F": chi_vf,
                "chi_2_minus_2g": chi_genus,
                "matches": chi_vf == chi_genus,
            }
        )

    assert gap_lambda_1 > 0.0, "La brecha espectral discreta debe ser positiva."
    assert plaquette_vac == 0.0 and plaquette_pert > 0.0, "Falla la acción de plaqueta juguete."
    assert sym_pq_ok is True and chi_k3 == 24, "Falla la consistencia del diamante de Hodge K3."
    assert all(item["matches"] for item in euler_checks), "Falla V - E + F == 2 - 2g."

    return {
        "yang_mills_toy": {
            "ring_n": ring_n,
            "spectral_gap_lambda_1": round(gap_lambda_1, 8),
            "gap_positive": gap_lambda_1 > 0.0,
            "plaquette_vacuum": plaquette_vac,
            "plaquette_perturbed_0_2": round(plaquette_pert, 8),
        },
        "hodge_k3_toy": {
            "conjugate_symmetry_h_pq_eq_h_qp": sym_pq_ok,
            "euler_from_hodge_diamond": chi_k3,
            "expected_k3_euler": 24,
        },
        "poincare_euler_toy": {
            "all_match_2_minus_2g": all(item["matches"] for item in euler_checks),
            "surfaces": euler_checks,
        },
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Ejecuta comprobaciones y cotas numéricas para los 7 Problemas del Milenio (modelos)."
    )
    parser.add_argument("--max-n", type=int, default=5, help="Máximo n inicial para tabla de crecimiento.")
    parser.add_argument("--e0", type=float, default=1.0, help="Energía inicial E(0) en Navier-Stokes reducido.")
    parser.add_argument("--nu", type=float, default=0.05, help="Viscosidad cinemática nu (> 0).")
    parser.add_argument("--dt", type=float, default=0.02, help="Paso temporal dt.")
    parser.add_argument("--steps", type=int, default=50, help="Número de pasos temporales.")
    parser.add_argument("--bsd-a", type=int, default=-1, help="Coeficiente a de y^2 = x^3 + ax + b.")
    parser.add_argument("--bsd-b", type=int, default=0, help="Coeficiente b de y^2 = x^3 + ax + b.")
    parser.add_argument("--riemann-terms", type=int, default=4000, help="Términos para serie eta de Dirichlet.")
    parser.add_argument("--ring-n", type=int, default=8, help="Tamaño de red 1D para brecha espectral juguete.")
    parser.add_argument("--selftest", action="store_true", help="Confirma explícitamente que todas las aserciones pasaron.")
    parser.add_argument("--json", action="store_true", help="Imprime salida en JSON.")
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    p_res = run_p_vs_np_checks(max_n=args.max_n)
    ns_res = simulate_dissipative_energy(
        e0=args.e0, nu=args.nu, dt=args.dt, steps=args.steps
    )
    bsd_res = run_bsd_checks(a=args.bsd_a, b=args.bsd_b)
    rm_res = run_riemann_checks(terms=args.riemann_terms)
    ym_hp_res = run_yang_mills_hodge_poincare_checks(ring_n=args.ring_n)

    payload = {
        "p_vs_np": p_res,
        "navier_stokes_reduced": ns_res,
        "birch_swinnerton_dyer": bsd_res,
        "riemann": rm_res,
        "yang_mills_hodge_poincare": ym_hp_res,
        "selftest_passed": True,
    }

    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print("=== Verificación P vs NP (modelos y cotas) ===")
        for k, v in p_res["sat_cases"].items():
            print(f"  - {k}: {v}")
        print(
            f"  - quadraticCost(10)={p_res['quadratic_cost_n10']} "
            f"(cota <=305 en [0..10]: {p_res['quadratic_bound_le_305_for_n_le_10']})"
        )
        print(f"  - Cruce 2^n > 2*n^3 + 2 en n={p_res['crossover_n_2pow_n_gt_2n3_plus_2']}")

        print("\n=== Verificación Navier-Stokes reducido (disipación energética) ===")
        print(
            f"  - E(0)={ns_res['e0']:.6f} -> E_final={ns_res['e_final']:.6f} "
            f"(disipado={ns_res['total_energy_dissipated']:.6f})"
        )
        print(
            f"  - no_negativa={ns_res['non_negative']} | "
            f"monotona_decreciente={ns_res['monotone_non_increasing']} | "
            f"E_final < 0.2: {ns_res['below_0_2_after_steps']}"
        )

        print("\n=== Verificación BSD (conteo en F_p y cota de Hasse) ===")
        prim = bsd_res["primary_curve"]
        sec = bsd_res["secondary_curve_y2_eq_x3_plus_1"]
        print(
            f"  - Curva 1: {prim['curve']} | enteros pequeños: {prim['known_small_integer_points']}"
        )
        print(
            f"  - Curva 2: {sec['curve']} | enteros pequeños: {sec['known_small_integer_points']}"
        )
        print(f"  - Todas las curvas cumplen Hasse: {bsd_res['all_curves_within_hasse']}")
        for row in prim["mod_p_samples"][:5]:
            print(
                f"    [C1] p={row['p']:2d} -> #E(F_p)={row['points_Fp']:2d}, "
                f"a_p={row['a_p']:+2d}, cota_Hasse={row['hasse_bound_2sqrt_p']}"
            )

        print("\n=== Verificación Riemann (serie eta y simetría) ===")
        print(
            f"  - zeta(2) est={rm_res['zeta_2_est']} vs exacto={rm_res['zeta_2_exact']} "
            f"(error={rm_res['zeta_2_abs_error']:.2e})"
        )
        for probe in rm_res["critical_line_probes"]:
            print(f"  - Sonda s={probe['s']} -> |eta(s)|={probe['eta_abs']} (N={rm_res['terms_used']})")
        print(
            f"  - Simetría conjugada ok={rm_res['conjugate_symmetry_ok']} "
            f"(diff={rm_res['conjugate_symmetry_diff']:.2e})"
        )

        print("\n=== Verificación Yang-Mills, Hodge y Poincaré (modelos) ===")
        ym = ym_hp_res["yang_mills_toy"]
        hg = ym_hp_res["hodge_k3_toy"]
        pc = ym_hp_res["poincare_euler_toy"]
        print(
            f"  - YM brecha lambda_1={ym['spectral_gap_lambda_1']} (pos={ym['gap_positive']}) | "
            f"plaqueta vac={ym['plaquette_vacuum']} / pert={ym['plaquette_perturbed_0_2']}"
        )
        print(
            f"  - Hodge K3 sim={hg['conjugate_symmetry_h_pq_eq_h_qp']} | "
            f"chi={hg['euler_from_hodge_diamond']} (esperado={hg['expected_k3_euler']})"
        )
        print(f"  - Poincaré V-E+F == 2-2g en todas las muestras: {pc['all_match_2_minus_2g']}")

        if args.selftest:
            print("\n[SELFTEST OK] Todas las aserciones de cotas y consistencia se cumplieron.")
