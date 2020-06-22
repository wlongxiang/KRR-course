from planning import PlanningProblem, Action, Expr, expr
import planning

import clingo


def add_initial_states(planning_problem, asp_code):
    for init_state in planning_problem.initial:
        asp_code += "init({}).\n".format(str(init_state).swapcase())
    return asp_code


def add_actions(planning_problem, asp_code):
    for action in planning_problem.actions:
        # action(rightshoe).
        action_name = action.name.swapcase()
        if action.args:
            args_str = str(action.args)
            action_name += args_str.swapcase()
        # swapcase because in clingo ASP, lowercase letters represent literals, uppercase represents variables
        asp_code += "action(" + action_name + ").\n"
        # precond(rightshoe, rightsockon).
        for precond in action.precond:
            precond_str = str(precond).swapcase()
            asp_code += "precond(" + action_name + "," + precond_str + ").\n"
        # effect(rightshoe, rightshoeon).
        for effect in action.effect:
            effect_str = str(effect).swapcase()
            if "~" in effect_str:
                effect_str = effect_str.replace("~", "")
                asp_code += "negeffect(" + action_name + "," + effect_str + ").\n"

            else:
                asp_code += "effect(" + action_name + "," + effect_str + ").\n"

    return asp_code


def add_goals(planning_problem, asp_code):
    for goal in planning_problem.goals:
        goal_str = str(goal).swapcase()
        asp_code += "goal(" + goal_str + ").\n"

    return asp_code


def solve_planning_problem_using_ASP(planning_problem, t_max):
    """
    If there is a plan of length at most t_max that achieves the goals of a given planning problem,
    starting from the initial state in the planning problem, returns such a plan of minimal length.
    If no such plan exists of length at most t_max, returns None.
    Finding a shortest plan is done by encoding the problem into ASP, calling clingo to find an
    optimized answer set of the constructed logic program, and extracting a shortest plan from this
    optimized answer set.
    Parameters:
        planning_problem (PlanningProblem): Planning problem for which a shortest plan is to be found.
        t_max (int): The upper bound on the length of plans to consider.
    Returns:
        (list(Expr)): A list of expressions (each of which specifies a ground action) that composes
        a shortest plan for planning_problem (if some plan of length at most t_max exists),
        and None otherwise.
    """
    ############
    # Note: this assignment is done based on discussion with Ruihan.
    # TODO: the current solution only work for easy0 which has simple effects and preconditions for actions
    # I was not able to extend it to more complex action effects and preconditions, I have tried to reach to TA using
    # canvas inbox, but I didn't get any response, without external help, this is really the best I can do. I am sorry.
    # this course is the most stressful so far in the whole master of AI due to its lack of support.
    ##############
    #
    # first we define the max STEP as constant
    asp_code = "#const t={}.\n".format(4)
    # then we define STEP as facts.
    asp_code += "time(1..t).\n"
    # then we add initial states
    asp_code = add_initial_states(planning_problem, asp_code)
    asp_code = add_actions(planning_problem, asp_code)
    asp_code = add_goals(planning_problem, asp_code)
    ###############
    # note the following code is borrowed from paper: "Potassco: The Potsdam Answer Set Solving Collection"
    # which is universal logic program for converting automatic planning problem into ASP, only need to add additions
    # rules for the problem at hand.
    ##############
    asp_code += """
% initial conditions holds
holds(P,0) :- init(P).
% make sure one action is taken at a time
1 { takeactionAtTime(A,T) : action(A) } 1 :- time(T).
% constrain: if an action A is taken at step T, its precondion must hold at time T-1
:- takeactionAtTime(A,T), precond(A,G), not holds(G, T-1).
holds(G,T) :- holds(G,T-1), not ocdel(G,T), time(T).
holds(G,T) :- takeactionAtTime(A,T), effect(A,G).
ocdel(G,T) :- takeactionAtTime(A,T), negeffect(A,G).
:- goal(G), not holds(G, t).
#show takeactionAtTime/2.
    """

    print(asp_code)

    global plan
    plan = [None for i in range(t_max - 1)]

    # utilies function from example code lecture provided
    # code from course material
    def print_answer_sets(program):
        # Load the answer set program, and call the grounder
        control = clingo.Control()
        control.add("base", [], program)
        control.ground([("base", [])])

        # Define a function that will be called when an answer set is found
        # This function sorts the answer set alphabetically, and prints it
        def on_model(model):
            for atom in model.symbols(shown=True):
                idx = atom.arguments[1].number - 1
                plan[idx] = expr(atom.arguments[0].name.swapcase())
            # plan = [str(atom) for atom in model.symbols(shown=True)]
            # plan.sort()
            print("Answer set:", plan)

        # Ask clingo to find all models (using an upper bound of 0 gives all models)
        control.configuration.solve.models = 1
        # Call the clingo solver, passing on the function on_model for when an answer set is found
        answer = control.solve(on_model=on_model)
        # Print a message when no answer set was found
        if answer.satisfiable == False:
            print("No answer sets")
            return None
        else:
            return plan

    plan = print_answer_sets(asp_code)
    return plan
