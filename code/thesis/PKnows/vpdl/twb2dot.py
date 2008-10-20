
import re

rule_app = re.compile(r"([a-zA-Z]+) \( ([0-9]+) -> ([0-9]+) \)")

def twb2dot(lines):
    print 'digraph twbvis {'
    print ' n0 [label="start"];'
    for ln in lines:
        m = rule_app.match(ln)
        if m:
          (nm,p,c) = m.groups()
          print ' n%s -> n%s [label="%s"]' % (p,c,nm)
    print '}'


if __name__ == "__main__":
    import sys
    twb2dot(sys.stdin)
        
