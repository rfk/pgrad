"""

  unlyx:  remove lyx-generated LaTeX from my thesis chapters

"""

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
        # OK, write it out
        outF.write(ln)
    # All done!
    
if __name__ == "__main__":
    import sys
    unlyx(sys.stdin,sys.stdout)
