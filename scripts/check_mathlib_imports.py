import os

def list_files_by_type_recursive(folder_path, file_extension):
    """Recursively lists all files in a folder and subfolders with the specified file extension."""
    matching_files = []
    for root, _, files in os.walk(folder_path):
        matching_files.extend(os.path.join(root, f) for f in files if f.endswith(file_extension))
    return matching_files

folder = "LeanCamCombi/Mathlib"
extension = ".lean"
files = list_files_by_type_recursive(folder, extension)

for file in files:
    code = None
    with open(file, "r") as reader:
        code = reader.read()
    lines = code.split("\n")
    header = [line for line in lines if line.lstrip().startswith("import")]

    for imp in header:
        imp_file = imp.lstrip()[len("import"):].strip()
        if (not imp_file.startswith("Mathlib.")) and \
            (not imp_file.startswith("LeanCamCombi.Mathlib")):
            raise OSError(f"""
MathlibImportError: A file in LeanCamCombi.Mathlib imports a file not in Mathlib or LeanCamCombi.Mathlib
\tImporting file: {file}
\tImported file: {imp_file}
""")
