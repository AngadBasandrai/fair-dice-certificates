Four-player fair-dice games
Angad Basandrai
Version 1.0.0

Python 3.13. Install dependencies and reproduce the results:

python -m pip install -r requirements.txt
python verify.py

Run without -O or -OO. The checker uses assertions.

M6.json, M7.json and M8.json contain the exact dominance and support-exclusion certificates. Each support record stores the supports and the rational multipliers y, z and lambda from Proposition 1. Omitted coefficients are zero.

roots.json contains the ordered supports, rational centers and rational preconditioners for the nine eight-outcome equilibria. The checker reconstructs the payoff polynomials and verifies boxes of radius 10^-30 for all nine rows and 2*10^-6 for rows 1,2,9.

verify.py checks both payoff constructions, all 35,260 certificates, the exhaustive support census, exact six- and seven-outcome equilibria, interval root certificates and global uniqueness in rows 1,2,9. It overwrites results.json with the reproduced results.

Global uniqueness uses Z3; no independent unsatisfiability certificate is available. Uniqueness in rows 3 through 8 remains unresolved.
