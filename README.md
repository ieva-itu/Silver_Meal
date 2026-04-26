# Silver_Meal
Silver Meal Rule formalization in Lean 4 and empirical validation in Python and Z3


```
# From Heuristic to Verification Condition: Silver-Meal
This repository contains the artifact accompanying the paper:
“From Heuristic to Verification Condition: A Lean 4 and SMT Characterization of the Silver–Meal Rule”

It includes:
- a Lean 4 formalization of the Silver-Meal heuristic,
- Python scripts for large-scale experimental validation,
- an SMT (Z3) encoding for solver-based verification.

---

## 📁 Repository Structure

```

SilverMeal.lean                         # Lean 4 formalization
exp_silvermeal.py                      # General experiment runner
exp_silvermeal_existence_theorem.py    # Existence theorem validation
exp_silvermeal_characterization_theorem.py  # Characterization validation
z3_silvermeal.py                       # SMT (Z3) encoding and checks

```

---

## ⚙️ Requirements

### 🧮 Lean 4

Tested with:
```
Lean (version 4.25.0-rc2)
````

Install Lean, Mathlib
Set up a Lean project with mathlib
Then place `SilverMeal.lean` inside the project.

---

### 🐍 Python
Tested with: Python 3.8
Dependencies: pip install z3-solver
Standard library modules used:
* `csv`
* `random`
* `time`
* `dataclasses`
* `typing`

---

## 🚀 Running Experiments

### 1. Existence theorem validation

```bash
python3 exp_silvermeal_existence_theorem.py
```
---
### 2. Characterization theorem validation

```bash
python3 exp_silvermeal_characterization_theorem.py
```
---
### 3. General experiments
```bash
python3 exp_silvermeal.py
```
---
### 4. SMT (Z3) verification
```bash
python z3_silvermeal.py
```
---

## 📊 Output

* Console summaries (success/failure counts)
* Optional CSV export (e.g., `silver_meal_existence_500k.csv`)
* Large-scale runs (500k instances) may take several hours (up to ~48h)




---
