

The plan:  Create a ConGolog system to plan for multiple agents in the
           concurrent, temporal situation calculus with natural actions.
           It will use Prolog's theorem proving to perform regression
           and thus will inherit the closed-world assumption.

           The working name for this language is MConGolog as it will
           inherit the syntax of ConGolog but extend it for the new
           calculus.

           Testing will be based on the "Cooking Agents" domain, where
           several agents cooperate to prepare a meal by executing
           recipies specified as MConGolog programs.


The files:   * sitcalc.pl - foundational axioms of the situation calculus
             * mcongolog.pl - semantics and solver for MConGolog programs
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

    TODO:  pi(D1//D2) is stuffing up the order of selection of solutions,
           making concurrent choices appear last.  Can we fix this?

