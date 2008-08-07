"""

  unlyx:  remove lyx-generated LaTeX from my thesis chapters

"""

import re
import os

def unlyx(inF,outF):
    inF = iter(inF)
    # Skip anything before and including \begin{document}
    ln = inF.next()
    while not ln.startswith("\\begin{document}"):
        ln = inF.next()
    # Process all lines up till \bibliographystyle or \end{document}
    while True:
        ln = inF.next()
        if ln.startswith("\\bibliographystyle"): break
        if ln.startswith("\\end{document}"): break
        #  Ignore any \newcommand lines, they are in the preamble/macros file
        if ln.startswith("\\newcommand"): continue
        if ln.startswith(" \\newcommand"): continue
        #  Remove stupid square-bracket escaping
        ln = unescape_sqb(ln)
        #  Recurse to any subfiles LyX might have touched
        fix_subfiles(ln)
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
      

if __name__ == "__main__":
    import sys
    unlyx(sys.stdin,sys.stdout)
