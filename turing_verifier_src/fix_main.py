with open("Main.lean", "r") as f:
    lines = f.readlines()

# Filter out misplaced imports or clean them up
cleaned_lines = [line for line in lines if not line.strip().startswith("import TuringVerifier.IntervalArithmetic")]

# Put the import strictly at line 1
final_lines = ["import TuringVerifier.IntervalArithmetic\n"] + cleaned_lines

with open("Main.lean", "w") as f:
    f.writelines(final_lines)

print("Main.lean reorganizado con el import al inicio.")
