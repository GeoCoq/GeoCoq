import subprocess

result = subprocess.run(
    ["lake", "env", "lean", "GeocoqTranslate/Scratch.lean"],
    capture_output=True,
    text=True,
    cwd="../lean/geocoq_translate"
)

print("STDOUT:")
print(result.stdout)

print("STDERR:")
print(result.stderr)

print("RETURN CODE:", result.returncode)