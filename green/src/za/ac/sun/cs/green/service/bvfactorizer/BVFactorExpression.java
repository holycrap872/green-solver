package za.ac.sun.cs.green.service.bvfactorizer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeSet;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Alias;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.ArrayVariable;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.resources.HashSetMap;
import za.ac.sun.cs.green.resources.IdentityHashSet;
import za.ac.sun.cs.green.service.bvfactorizer.resources.AVStack;
import za.ac.sun.cs.green.service.bvfactorizer.resources.ArrayAccesses;
import za.ac.sun.cs.green.service.bvfactorizer.resources.BVFactorHelper;
import za.ac.sun.cs.green.service.bvfactorizer.resources.SelectStore;
import za.ac.sun.cs.green.service.bvfactorizer.resources.UndeterminedArrayMerger;

/**
 * This class records the factors for a given constraint. It supports
 * incrementally updating, i.e., given an extension of a constraint the factors
 * are computed incrementally based on that extension.
 */
public class BVFactorExpression {

	private static int STARTSIZE = 100;

	/**
	 * Factors are sets of mutually dependent expressions. Each such set is
	 * grouped into a map entry whose key is the set of array accesses 
	 * involved in expressions in the set.  A selectstore is used to represent
	 * these array accesses.
	 * 
	 * An invariant for this map is that the keys are disjoint sets of
	 * array accesses.
	 */
	private Map<IdentityHashSet<SelectStore>, SortedSet<Expression>> var2Factor;

	/**
	 * For convenience we maintain the union of the image of var2Factor as a
	 * set.
	 */
	private Set<SelectStore> variables;

	/**
	 * The number of conjuncts in the entire constraint
	 */
	private int conjunctCount;

	/**
	 * Statistics caches: these help avoid having to recompute conjunct and
	 * variable counts which can be accumulated when the actual dependent factor
	 * calculations are performed.
	 * 
	 * The first shadows var2Factor and records the number of conjuncts in each
	 * factor. The last two cache counts from the dependent factor calculations.
	 */
	private Map<IdentityHashSet<SelectStore>, Integer> var2ConjunctCounts;
	private Map<Expression, Integer> dependentVarCounts;
	private Map<Expression, Integer> dependentConjunctCounts;

	/**
	 * Keeps track of which select statements are associated with a particular array.
	 * This will be useful whenever a select statement uses a non-constant index,
	 * in which case all references to that array must be collapsed into a single
	 * constraint.
	 */
	private ArrayAccesses arrayAccesses;

	private HashSetMap<SelectStore> var2Vars;
	
	private Properties smashProperties;
		
	/**
	 * Create a new empty FactoredConstraint
	 */
	public BVFactorExpression() {
		var2Factor = new HashMap<IdentityHashSet<SelectStore>, SortedSet<Expression>>();
		variables = new HashSet<SelectStore>(STARTSIZE);
		conjunctCount = 0;
		var2ConjunctCounts = new HashMap<IdentityHashSet<SelectStore>, Integer>();
		dependentVarCounts = new HashMap<Expression, Integer>();
		dependentConjunctCounts = new HashMap<Expression, Integer>();

		arrayAccesses = new ArrayAccesses();

		var2Vars = new HashSetMap<SelectStore>();
	}

	/**
	 * Create a new FactoredConstraint incrementally from a given
	 * FactoredConstraint, base, and a new Expression, fresh.
	 * 
	 * A deep copy of the base is created to ensure changes here do not affect
	 * other users of the base. The copy only goes as deep as the structures
	 * used in this class. Specifically, things like Expressions and Variables
	 * do not need to be copied.
	 */
	public BVFactorExpression(Green solver, BVFactorExpression base, Expression fresh, Properties smashProperties_) {

		if (base == null) {
			base = new BVFactorExpression();
		}

		// Make a deep copy of the base map. The underlying Variables and
		// Expressions can be shared
		var2Factor = new HashMap<IdentityHashSet<SelectStore>, SortedSet<Expression>>();
		var2ConjunctCounts = new HashMap<IdentityHashSet<SelectStore>, Integer>();

		for (Set<SelectStore> keys : base.var2Factor.keySet()) {
			SortedSet<Expression> copyExprs = new TreeSet<Expression>(base.var2Factor.get(keys));
			IdentityHashSet<SelectStore> copyVars = new IdentityHashSet<SelectStore>(keys);
			var2Factor.put(copyVars, copyExprs);

			// Copy the statistics structure
			var2ConjunctCounts.put(copyVars, base.var2ConjunctCounts.get(keys));
		}

		arrayAccesses = new ArrayAccesses(base.arrayAccesses);

		// Make a copy of the base variables.
		variables = new HashSet<SelectStore>(base.variables);
		var2Vars = new HashSetMap<SelectStore>(base.var2Vars);

		// Initialize statistics structures
		conjunctCount = base.conjunctCount;
		dependentVarCounts = new HashMap<Expression, Integer>();
		dependentConjunctCounts = new HashMap<Expression, Integer>();
		
		this.smashProperties = smashProperties_;

		/**
		 * Extract both the constraints and the associated array accesses within
		 * those expressions from the fresh expression.
		 */

		Map<Expression, IdentityHashSet<SelectStore>> conjunct2Vars = new HashMap<Expression, IdentityHashSet<SelectStore>>();
		Collector collector = new Collector(conjunct2Vars);
		collector.explore(fresh);

		/**
		 * Add each of the fresh constraints to the FactorizedFormula
		 */
		for (Expression expr : conjunct2Vars.keySet()) {
			assert expr instanceof Operation;
			conjunctCount++;
			addConstraint(expr, conjunct2Vars.get(expr));
		}
		
		UndeterminedArrayMerger.mergeNecessary(solver, var2Vars, var2Factor, variables, var2ConjunctCounts, arrayAccesses, smashProperties);
	}

	public static int count = 0;
	/**
	 * The new expression (and its associated vars) are added to the conjunct
	 * map.
	 * 
	 * There are two cases: 1) The new expression is independent of the existing
	 * map, in which case it is a new factor. 2) The new expression is dependent
	 * on some existing factors, in which case all dependent factors must be
	 * merged.
	 * 
	 * @param vars
	 *            The set of variables involved in the new conjunct
	 * @param exprs
	 *            The logical expression being conjoined
	 */
	private void addConstraint(Expression expr, IdentityHashSet<SelectStore> vars) {
	
		Set<SelectStore> intersection = new IdentityHashSet<SelectStore>(vars);

		//Update mapping of all individual array accesses
		//It would perhaps be more efficient to do this only for selects that are not in
		//the intersection of vars and variables but it's not worth the computational time
		//to do this.


		// Compute intersection of variables with existing factor's vars
		intersection.retainAll(variables);
		Set<SelectStore> complementIntersection = this.complement(vars, intersection); 

		for(SelectStore s: complementIntersection){
			arrayAccesses.insertAccess(s);
		}


		/*
		 * If none of the variables have been seen yet
		 */
		if (intersection.isEmpty()) {
			// System.out.println("New independent factor relative to keys "+var2Factor.keySet()+" with vars "+vars);
			// Expression is a new independent factor so add it to map and
			// factors
			SortedSet<Expression> newFactor = new TreeSet<Expression>();
			newFactor.add(expr);
			var2Factor.put(vars, newFactor);
			var2Vars.addAll(vars);
			variables.addAll(vars);


			// Update statistics
			var2ConjunctCounts.put(vars, new Integer(1));

			// System.out.println("   Updated keys "+var2Factor.keySet());

		} else {
			BVFactorHelper.merge(var2Vars, var2Factor, variables, var2ConjunctCounts, vars, expr, complementIntersection);
		}


	}

	private Set<SelectStore> complement(Set<SelectStore> vars, Set<SelectStore> complementOf){
		Set<SelectStore> complement = new IdentityHashSet<SelectStore>();
		for(SelectStore v: vars){
			if(!complementOf.contains(v)){
				complement.add(v);
			}
		}
		return complement;
	}

	/*
	 * Merge should do the following:
	 * 
	 * It should take the set of variables involved in a particular conjunct
	 * that we want to be merged along with the conjunct itself.  It should
	 * then go through all previous conjuncts and merge together all of the
	 * ones where there is an intersection with the incoming set of variables
	 */

	public int getVariableCount() {
		return variables.size();
	}

	public int getConjunctCount() {
		return conjunctCount;
	}

	public Expression getDependentFactor(Expression expr) {
		/**
		 * Rather cavalier reuse of the local collector class. Should really
		 * have a common variable name collector that is reused.
		 * 
		 * In the end vars is the set of variables in the given constraint
		 */
		Map<Expression, IdentityHashSet<SelectStore>> conjunct2Vars = new HashMap<Expression, IdentityHashSet<SelectStore>>();
		Collector collector = new Collector(conjunct2Vars);
		collector.explore(expr);

		// Initialize statistics
		int numVars = 0;
		int numConjuncts = 0;

		Expression dependentExpr = null;

		// If there are no variables in the fresh conjunct, we do not modify the
		// instance any further: its conjunct forms a trivial slice
		if (conjunct2Vars.size() == 0) {
			dependentExpr = expr;
		} else {

			Set<SelectStore> exprVars = new IdentityHashSet<SelectStore>();
			for (Expression e : conjunct2Vars.keySet()) {
				exprVars.addAll(conjunct2Vars.get(e));
			}

			// System.out.println("Computing slice for map with vars "+var2Factor.keySet()+" for fresh "+exprVars);
					for (Set<SelectStore> vars : var2Factor.keySet()) {
						// System.out.println("  considering these vars "+vars);
						Set<SelectStore> intersect = new IdentityHashSet<SelectStore>(vars);
						intersect.retainAll(exprVars);
						if (!intersect.isEmpty()) {
							// System.out.println("     found a match with conjuncts "+var2Factor.get(vars));
							for (Expression e : var2Factor.get(vars)) {
								dependentExpr = (dependentExpr == null) ? e : new Operation(Operation.Operator.AND, dependentExpr, e);

							}

							// Update local statistics
							numVars += vars.size();
							numConjuncts += var2ConjunctCounts.get(vars);
						}
					}
		}

		// Update statistics
		dependentVarCounts.put(expr, new Integer(numVars));
		dependentConjunctCounts.put(expr, new Integer(numConjuncts));

		return dependentExpr;
	}

	public int getDependentVariableCount(Expression expr) {
		Integer varCount = dependentVarCounts.get(expr);
		if (varCount == null) {
			getDependentFactor(expr);
			return dependentVarCounts.get(expr).intValue();
		} else {
			return varCount.intValue();
		}
	}

	public int getDependentConjunctCount(Expression expr) {
		Integer varCount = dependentConjunctCounts.get(expr);
		if (varCount == null) {
			getDependentFactor(expr);
			return dependentConjunctCounts.get(expr).intValue();
		} else {
			return varCount.intValue();
		}
	}

	public Set<Expression> getFactors() {
		Set<Expression> factors = new LinkedHashSet<Expression>();
		for (Set<SelectStore> vars : var2Factor.keySet()) {
			Expression curFactor = null;
			for (Expression e : var2Factor.get(vars)) {
				curFactor = (curFactor == null) ? e : new Operation(Operation.Operator.AND, curFactor, e);
			}
			factors.add(curFactor);
		}
		return factors;
	}

	public int getNumFactors() {
		return var2Factor.size();
	}

	public String toString() {
		String string = "";
		for (Set<SelectStore> vars : var2Factor.keySet()) {
			string = string + vars.toString() + "->" + var2Factor.get(vars).toString() + ", ";
		}
		if (string.length() < 2) {
			return string;
		} else {
			return string.substring(0, string.length() - 2);
		}
	}
	
	/**
	 * Visitor that builds the maps from conjuncts to variables. Should probably
	 * reuse this, but for now it is adapted from the code in the default
	 * slicer.
	 * 
	 * @author Jaco Geldenhuys <jaco@cs.sun.ac.za>
	 */
	private class Collector extends Visitor {

		/**
		 * The map from conjuncts to the array accesses it contains.
		 */
		private Map<Expression, IdentityHashSet<SelectStore>> conjunct2Vars = null;

		/**
		 * The currentConjunct being visited.
		 */
		private IdentityHashSet<SelectStore> currentConjunctVars = null;

		/**
		 * Keeps track of how deep into a particular conjunct we are. By this
		 * I mean how many subexpressions we have traversed into, not including
		 * the over-arching ands which joining all of the conjunct together.
		 * 
		 * Needed for Klee things of the form: (=  false (=
		 */
		private Stack<Integer> s;

		/**
		 * Keeps track of the root access of a variable.  Klee can have conjuncts
		 * of the form select( select( select (a, 1), 2), 3) and 
		 * store( store( store(a, index, value), index, value), index, value).  
		 * Therefore, we need to know for each store operation what array it is 
		 * actually accessing.  The AVStack acts as a stack that can store the 
		 * array share it with the three stores/selects it is associated with.
		 * 
		 * It does this by storing the most recent arrayvariable associated with
		 * each part of an operation.  Therefore, for a complicated operation like
		 * store, each pop of the av stack will hold the last array access seen
		 * within that subexpression.
		 */
		private AVStack store;

		/**
		 * Constructor that sets the two mappings that the collector builds.
		 * 
		 * @param conjunct2Vars
		 *            a map from conjuncts to the variables they contain
		 * @param var2Conjuncts
		 *            a map from the variables to the conjuncts in which they
		 *            appear
		 */
		public Collector(Map<Expression, IdentityHashSet<SelectStore>> conjunct2Vars) {
			this.conjunct2Vars = conjunct2Vars;
			this.s = new Stack<Integer>();
			this.store = new AVStack();
		}

		/**
		 * Explores the expression by setting the default conjunct and then
		 * visiting the expression.
		 * 
		 * @param expression
		 *            the expression to explore
		 */
		public void explore(Expression expression) {
			try {
				expression.accept(this);
			} catch (VisitorException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		@Override
		/*
		 * If it is an array variable, it is the new "last seen" array variable.
		 * Otherwise, we just duplicate the last array variable seen.
		 */
		public void postVisit(Variable variable){
			if(variable instanceof ArrayVariable){
				store.push((ArrayVariable)variable);
			}else{
				store.push(store.peek());
			}
		}

		@Override
		/*
		 *  Since it is not an array, it cannot be used to answer the question
		 *  "What array is associated with a particular select/store"  Therefore, 
		 *  we duplicate the last array seen so that it will be at the top of the
		 *  stack when we finally reach the store operation.
		 *  
		 *  The reason we need to duplicate it is the select statement in klee is
		 *  of the form store(array, index, value).  We therefore want to push the
		 *  last array seen through 
		 */
		public void postVisit(Constant constant){
			store.push(store.peek());
		}

		@Override
		public void postVisit(Operation operation){
			Operation.Operator op = operation.getOperator();
			if(op == Operation.Operator.SELECT || op == Operation.Operator.STORE ){

				/*
				 * Although this is different from the other operations, we disregard the TOP
				 * of the stack because it stores and selects are special.  They are special
				 * because their return value is dependent on the stack in the array operand,
				 * not the one last seen (which could perhaps have come from the index operand).
				 * 
				 * For example, (select (store array1 x+1 (select array2 8)))
				 * 
				 * Even though array2 would be the last one seen, we care about array1
				 */             
				ArrayVariable last = this.getArrayStoreSelect(store, operation);
				
				Expression index = operation.getOperand(1);
				SelectStore ss = new SelectStore(last, index);
				this.currentConjunctVars.add(ss);
			}else{
				if (op.isComparator() && op!=Operation.Operator.AND) {
					s.pop();
					//If we've traversed the entire conjunct and reach the top
					//then save all of the information we have gathered
					if(s.isEmpty()){
						conjunct2Vars.put(operation, this.currentConjunctVars);
					}
				}

				//For each subexpression in an operation except one,
				//remove arrays from the avstore.
				ArrayVariable last = null;
				for(int i=0; i<op.getArity(); i++){
					if(i==0){
						last = store.pop();
					}else{
						store.pop();
					}
				}
				store.push(last);
			}

		}

		/*
		 * Checks to see if we're at the top of a conjunct within
		 * the expression we are exploring.  If we are, then we 
		 * initialize currentConjunctVars to hold all of the information we find 
		 * while exploring the conjunct.  Otherwise, we have a stack s to keep
		 * track of how deep into the conjunct we are.
		 */
		@Override
		public void preVisit(Operation operation) {
			Operation.Operator op = operation.getOperator();
			if (op.isComparator() && op!=Operation.Operator.AND) {
				if(s.isEmpty()){
					currentConjunctVars = new IdentityHashSet<SelectStore>();
				}
				//Keeps track of how deep into a particular conjunct we are.
				s.push(new Integer(1));
			}
		}


		@Override
		/*
		 * Basic idea is the following
		 * 1) If the alias does not yet have the information then
		 *              - The visitor will continue on to explore the expression
		 *              - Therefore, we save the current state of store and create a new store 
		 */
		public void preVisit(Alias alias){
			if(!alias.hasFactorizerInformation()){
				alias.exploreSubexpression(true);
				alias.setFactorizerVisitorState(store, this.currentConjunctVars);
				currentConjunctVars = new IdentityHashSet<SelectStore>();
				store = new AVStack();
			}
		}

		@Override
		/*
		 * There is a really weird subtlety here.  It may seem like we should be
		 * more careful with the currentConjunctVars, saving their state and returning
		 * them like we do with store.  This is not necessary however, for two reasons.
		 * First, currentConjunctVars is cleared every time we enter a new toplevel conjunct
		 * Second, while the alias does not necessarily contain all of the variables in the
		 * currentConjunctVars, they are related to them.  This is because, even though they
		 * are not necessarily in the same toplevel conjunct, the factorizer will eventually
		 * place them together since they same variables (those in the  
		 * Therefore, they will eventually 
		 */
		public void postVisit(Alias alias){
			if(!alias.hasFactorizerInformation()){
				/*
				 * This means that we have just finished traversing the expression and therefore
				 *      must add all the achieved information to the alias as well as restore the stack
				 *      to what it should have been
				 */
				alias.setFactorizerAliasInformation((AVStack)store.clone(), currentConjunctVars);
				store = alias.getFactorizerStateStack();
				currentConjunctVars = alias.getFactorizerStateVariables();
				alias.exploreSubexpression(false);

			}
			currentConjunctVars.addAll(alias.getFactorizerAliasVariblesUsed());
			store.stickOntoEnd(alias.getFactorizerAliasStack());
		}

		/*
		 * Gets the array associated with a particular store/select statement.
		 * Does this by looking onto the avstack and popping once for each of
		 * the pieces in the operation.
		 * 
		 * It then leaves on the last one so that store/selects above will know
		 * what variable they are referencing in a store(store(store ...))) chain.
		 */
		private ArrayVariable getArrayStoreSelect(AVStack store, Operation operation){
			Operation.Operator op = operation.getOperator();
			//Store's have 3 pieces
			if(op == Operation.Operator.STORE){
				store.pop();
				store.pop();
			}else{
				store.pop();
			}

			return store.peek();
		}
	}

}
