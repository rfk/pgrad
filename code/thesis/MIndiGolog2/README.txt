
This is a MIndiGolog interpreter implemented using Mozart/Oz.
It was developed as part of Ryan Kelly's PhD thesis "Asynchronous Multi-Agent
Reasoning in the Situation Calculus".  Further details are available at:

   http://www.rfk.id.au/research/thesis/

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

---------------------------------

To get up and running, you will need a working installation of Mozart/Oz,
available from:

   http://www.mozart-oz.org/

For visualisation of joint executions, you will also need graphviz installed:

  http://www.graphviz.org/

It will also be helpful to have a unix-like environment to make use of the
included Makefile.

The included files are:

  main.oz:        top-level control file
  Sitcalc.oz:     domain-independent axioms of the situation calculus
  MIndiGolog.oz:  domain-independent semantics of MIndiGolog
  Step.oz:        procedure for manipulating program-step records
  LP.oz:          miscellaneous logic-programming procedures
  IntMap.oz:      simple integer-mapped hash table
  JointExec.oz:   implements joint executions as an abstract data type
  Planner.oz:     the main joint-execution planning loop
  Domain.oz:      domain-specific axioms
  Procedures.oz:  domain-specific MIndiGolog procedure definitions

Since the interpreter is currently limited to offline planning, I have not
copied across the multi-agent control procedures from MIndiGolog1 - the
planner simply runs on a single machine.

To plan and display a joint execution for the MIndiGolog procedure "main",
execute `make plan`.  This will run the main planning loop to construct a
joint execution, write it out the file plan.dot in Graphviz format, then
use graphviz's "dot" program to convert it into a PNG file in plan.png.
This file can be viewed using any popular image viewer.

