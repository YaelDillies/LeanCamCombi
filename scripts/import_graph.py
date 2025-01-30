import os
import re

def main():
  folder_path = "./website/_includes"
  if not os.path.exists(folder_path):
    os.makedirs(folder_path)

  dot_path = f"{folder_path}/import-graph-viz.dot"
  md_path = f"{folder_path}/import-graph-viz.md"

  #os.system(f"lake exe graph {dot_path} --exclude-meta")

  dot = ""
  with open(dot_path, "r") as r:
    dot = r.read()

  dot = dot.replace("\n", "<br/> \n * ")
  dot = dot.replace("* }", "}")

  for match in re.findall("\"LeanCamCombi(?:\.[A-Za-z0-9_]+)+\"", dot):
    module_name = match[1:-1] # taking out the quotation marks
    file_path = module_name.replace(".", "/") + ".lean"
    file_url = f"https://github.com/YaelDillies/LeanCamCombi/blob/master/{file_path}"
    dot = dot.replace(match, f"[`{module_name}`]({file_url})")

  dot = dot.replace("\"LeanCamCombi\"", f"[`LeanCamCombi`](https://github.com/YaelDillies/LeanCamCombi/blob/master/LeanCamCombi)")

  with open(md_path, "w+") as w:
    w.write(dot)

if __name__== "__main__":
  main()
