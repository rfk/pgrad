

The plan:  Create an IndiGolog system to plan for multiple agents in the
           concurrent, temporal situation calculus with natural actions.
           It will use Prolog's theorem proving to perform regression
           and thus will inherit the closed-world assumption.

           The working name for this language is MIndiGolog as it will
           inherit the syntax of IndiGolog but extend it for the new
           calculus.

           Testing will be based on the "Cooking Agents" domain, where
           several agents cooperate to prepare a meal by executing
           recipies specified as MIndiGolog programs.


The files:   * sitcalc.pl - foundational axioms of the situation calculus
             * mindigolog.pl - semantics and solver for MIndiGolog programs
             * domain.pl - axiomatisation of the domain in the calculus
             * main.pl - top-level control file, pulling it all together

The environment:   Development is being done under Ciao prolog, as it
                   is open source and provides a real-valued constraint
                   solver.  It also has interesting abilities wrt distributed
                   execution which may be used at a later stage.

    TODO:  your axiomatization of time is not up to snuff.  Need to be
           more specific about it, esp regarding natural actions.

    TODO: interesting stuff from cc-Golog etc:

        * continuously-changing properties and the waitFor instruction
        * mentions sGolog and the ability of search() to return conditional
          plan trees - see also search in Flux
        * actions which can be executed earlier are prefered in concurrent
          execution
        * "Continuous Fluents", also from Pinto, somehow interact with
          natural actions..?

    TODO: It would be useful to have some way of pruning the search
          tree, e.g. when a program gets stuck early due to a bad
          choice but must wait for a concurrent program to be
          searched to exhaustion...
          Research DTGolog perhaps for some ideas on this.
           

    TODO:  Note that pi() is also synchronised

    TODO:  Talk about allowing tests in concurrent action terms,
           only transition when the test is true.  Like a primitive
           blocking mechanism akin to if(test,act,false) but simpler.
           
    TODO:  produce formal proof that trans() generates only legal situations
           Possibly use results from "Plannig with Natural Actions in the
           Situation Calculus" to help out.

    TODO:  finish axiomatisation of oven usage
           


