"""

  unlyx:  remove lyx-generated LaTeX from my thesis chapters

"""

import re
import os
import os.path

def unlyx(inF,outF):
    inF = iter(inF)
    # Skip anything before and including \begin{document}
    ln = inF.next()
    while not ln.startswith("\\begin{document}"):
        ln = inF.next()
    # Process all lines until we hit one of the "end of doco" markers
    while True:
        ln = inF.next()
        if ln.startswith("\\bibliographystyle"): break
        if ln.startswith("\\end{document}"): break
        if ln.startswith("\\label{ch:references}"): break
        #  Ignore any \newcommand lines, they are in the preamble/macros files
        if ln.startswith("\\newcommand"): continue
        if ln.startswith(" \\newcommand"): continue
        #  Ignore line spacing declarations
        if ln.strip().startswith("\\onehalfspace"): continue
        #  Remove stupid square-bracket escaping
        ln = unescape_sqb(ln)
        #  Recurse to any subfiles LyX might have touched
        fix_subfiles(ln)
        #  Fix any filenames manged by LyX
        ln = fix_mangled_includes(ln)
        # OK, write it out
        outF.write(ln)
    # All done!

# Matches things like {{[}{LABEL}]}
sqb_re = re.compile(r"\{\{\[\}\{([^\}]+)\}\]\}")
def unescape_sqb(ln):
    """Unescape square brackets that have been mangled by LyX"""
    ln2 = sqb_re.sub(r"{\1}",ln)
    while ln2 != ln:
        ln = ln2
        ln2 = sqb_re.sub(r"{\1}",ln)
    return ln

input_re = re.compile(r"\\input\{([^\}]+)\}")
sqb2_re = re.compile(r"\{\[\}")
def fix_subfiles(ln):
    """Fix LyX formatting in included subfiles"""
    m = input_re.search(ln)
    if m:
      fn = m.group(1)
      fI = file(fn,"r")
      fO = file(fn + ".tmp","w")
      for ln in fI:
        ln = sqb2_re.sub("[",ln)
        fO.write(unescape_sqb(ln))
      fI.close()
      fO.close()
      fI = file(fn,"w")
      fO = file(fn + ".tmp","r")
      for ln in fO:
        fI.write(ln)
      fI.close()
      fI.close()

proginput_re = re.compile(r"\\programinput\{([^\}]+)\}")
def fix_mangled_includes(ln):
    """Fix include filename mangling that LyX does for no good reason.
    LyX mangles "file_name" => "filename".  Search through containing dir
    to find the correct version.
    """
    m = proginput_re.search(ln)
    if m:
      fn = m.group(1)
      dName = os.path.dirname(fn)
      fName = os.path.basename(fn)
      for fn2 in os.listdir(dName):
        if fn2.replace("_","") == fName:
          ln = "\\programinput{" + os.path.join(dName,fn2) + "}\n"
          break
    return ln

if __name__ == "__main__":
    import sys
    unlyx(sys.stdin,sys.stdout)
