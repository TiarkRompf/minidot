#!/usr/bin/env python

__doc__ = """usage: twelf2tex.py <twelf_signatures.txt>
converts Twelf signatures to inference rules in the style of TAPL
"""

import re

def go(twelf_txt):
  rem = twelf_txt
  commands = []
  rules = []
  grouprules = {}
  cmdrules = []
  while '.' in rem:
    i = rem.index('.')
    line = rem[:i]
    rem = rem[i+1:]
    if '=' in line:
      # ignore abbreviations, such as let sugar
      continue
    name, c, r, g = process(line)
    if c:
      commands.append(c)
    if name:
      cmdrules.append("\\newcommand{\\rule" + name + "}[0]{" + r + "}")
      r = "{\\rule" + name + "}"
    if g:
      grouprules[g] = grouprules.get(g, [])
      grouprules[g].append(r)
    rules.append(r)
  print "\n".join(commands)
  print
  print "\n".join(cmdrules)
  print
  print "\n".join("\\newcommand{\\allrules" + g + "}[0]{\n" + "\n".join(rs) + "\n}" for g, rs in grouprules.iteritems())
  print
  print "\\newcommand{\\allrules}[0]{\n" + "\n".join(rules) + "\n}"


def name2cmd(x):
  if x[0] == '-':
    return None
  x = x.replace("'", 'p')
  x = x.replace('-', '')
  x = x.replace('/', 'F')
  x = x.replace('0', 'Zero')
  x = x.replace('1', 'One')
  x = x.replace('2', 'Two')
  x = x.replace('3', 'Three')
  x = "aaa"+x
  return x

def typ2tex_rec(x):
  if x[0] == '(':
    i = x.index(' ')
    name = name2cmd(x[1:i].strip())
    args = []
    rem = x[i+1:].strip()
    while rem != "" and rem[0] != ')':
      _, a, rem = typ2tex_rec(rem)
      args.append(a)
    if rem != "":
      rem = rem[1:].strip()
    return name, "{\\" + name + " " + " ".join(["{"+a+"}" for a in args]) + "}", rem
  else:
    i = 0
    n = len(x)
    while i<n and x[i] != ' ' and x[i] != ')':
      i += 1
    name = None
    txt = x[:i].strip()
    if txt[0].islower():
      name = name2cmd(txt)
      txt = "\\" + name
    return name, txt, x[i:].strip()

def typ2nametex(x):
  if ' ' in x:
    x = "("+x+")"
  name, res, _ = typ2tex_rec(x)
  return name, res

def typ2tex(x):
  _, res = typ2nametex(x)
  return res

def process(x):
  ic = x.index(':')
  name = x[:ic].strip()
  body = x[ic+1:].strip()
  parts = [a.strip() for a in re.split(r"}|->", body)]
  n = len(parts)-1
  premises = []
  conclusion = ""
  for i,a in enumerate(parts):
    if a[0] == '(':
      a = a[1:]
    if a[-1] == ')':
      a = a[:-1]
    if a[0] == '{':
      ic = a.index(':')
      varname = a[1:ic].strip()
      vartype = a[ic+1:].strip()
      pname, p = None, "\\aaais {" + varname + "} {" + typ2tex(vartype) + "}"
    else:
      pname, p = typ2nametex(a)
    if i<n:
      premises.append(p)
    else:
      cname, conclusion = pname, p

  return name2cmd(name), new_command(name, n), new_rule(name, premises, conclusion), cname

def new_command(name, n):
  namecmd = name2cmd(name)
  if namecmd is None:
    return None
  args = ""
  if n>0:
    args = "(" + ",".join(["#" + str(i+1) for i in range(0, n)]) + ")"
  nmax = n
  if n>9:
    nmax = 9
  return "\\newcommand{\\" + namecmd + "}[" + str(nmax) + "]{\\text{" + name + args + "}}"

def new_rule(name, premises, conclusion):
  r = ""
  if name2cmd(name) is None:
    named = ""
  else:
    named = "[" + name + "]"
  if premises==[]:
    r += "\\infax" + named
  else:
    r += "\\infrule" + named + "{\n"
    r += "\\\\\n".join(premises)
    r += "\n}"
  r += "{"
  r += conclusion
  r += "}"
  return r

if __name__ == '__main__':
  import sys
  argc = len(sys.argv)
  if argc!=2:
    print __doc__
  else:
    with open(sys.argv[1], 'r') as twelf_file:
      twelf_txt = twelf_file.read()
      go(twelf_txt)
