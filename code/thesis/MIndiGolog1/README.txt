
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

It will also be helpful to have a unix-like environment to make use of the
included Makefile.

The included files are:

  main.oz:        top-level control file
  Sitcalc.oz:     domain-independent axioms of the situation calculus
  MIndiGolog.oz:  domain-independent semantics of MIndiGolog
  Domain.oz:      domain-specific axioms
  Procedures.oz:  domain-specific MIndiGolog procedure definitions
  Time.oz:        timepoints as an abstract data type
  LP.oz:          miscellaneous logic-programming procedures
  Control.oz:     agent control procedures

Since the interpreter is designed to run in a multi-agent setting, you will
need to do some preliminary setup to get things working correctly.  In the
example domain there are three agents named "jon", "joe" and "jim".

  1)  Select a computer on which to execute the control program for each agent.
      They can all be on the same machine, or on several networked machines.

  2)  Set up DNS so that each agent name resolves to the public IP address
      of the computer that is to host that agent.  Under Linux, I placed the
      following entries in my /etc/hosts file:

         192.168.0.5     jon
         192.168.0.4     jim
         192.168.0.4     joe

  3)  Place the MIndiGolog source code at the same location on each machine,
      and update the "import" section of each .oz file to point to this
      standard location.

  4)  Ensure that the Mozart installation on each machine is properly
      set up for remote access via ssh, following the instructions at:

          http://www.mozart-oz.org/documentation/system/node48.html


You should now be able to compile the MIndiGolog execution planner.  Using
the included Makefile, this is as simple as `make main.exe`.

You can then execute main.exe for each individual agent.  First start the team
leader (jon) using the following command on the appropriate computer:

  ./main.exe --agent=jon

Once the team leader is running, start the other team members on their
respective machines:

  ./main.exe --agent=jim
  ./main.exe --agent=joe

The agents will synchronise and establish their shared communication mechanism,
then proceed to execute the MIndiGolog procedure "main".  The actions performed
will be printed to stdout.

To modify the procedure being executed, edit the file "Procedures.oz" and
change the definition of "main".

---------------------------------

To re-create the timing tests for parallel search described in the thesis,
change "Procedures.oz" to define the "main" procedure as:

   search(pcall(hardToPlan))

Then simply execute `make time-test`.  This will perform three runs of
execution with parallel search enabled, and three with parallel search 
disabled, recording the execution times in TIME.p and TIME.s respectively.
For simplicity it runs the main control loop of each agent on 
a single machine, but the parallel search functionality will use the machines
identified by a DNS lookup on the agent's names.

