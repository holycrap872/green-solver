package za.ac.sun.cs.green.service.bvfactorizer.resources;

import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.resources.HashSetMap;
import za.ac.sun.cs.green.resources.IdentityHashSet;

public class BVFactorHelper {

	/**
	 * @param var2Vars - A mapping from a particular variable to all other variables with which it appears
	 * @param var2Factor - A mapping from a particular variable to the factor in which it appears (for quick factor combination)
	 * @param variables - A set of all variables in a constraints
	 * @param var2ConjunctCounts - A 
	 * @param vars - The set of variables, along with all of their related variables, to merge
	 * @param newExpression - The expression that is being processed: ie. having it's variables thrown into the mix
	 * @param newVars - The set of variables in that expression
	 */
	public static void merge(HashSetMap<SelectStore> var2Vars, Map<IdentityHashSet<SelectStore>, SortedSet<Expression>> var2Factor, Set<SelectStore> variables, Map<IdentityHashSet<SelectStore>, Integer> var2ConjunctCounts, Set<SelectStore> vars, Expression newExpression, Set<SelectStore> newVars){
		// Merge the factors that are related to vars: find them, combine
		// them, update map and factors structures
		SortedSet<Expression> mergedFactor = new TreeSet<Expression>();

		// Add the potentially new conjunct to the merged factor
		if(newExpression!=null){
			mergedFactor.add(newExpression);
		}

		//  Set<Select> vars2Merge = new HashSet<Select>(vars);
		IdentityHashSet<SelectStore> mergedVars = new IdentityHashSet<SelectStore>();

		for(SelectStore s: vars){
			if(mergedVars.add(s)){
				/*
				 * If there was an integer array access common to both, then
				 * they must be merged into a single factor.
				 */
				Set<SelectStore> related = var2Vars.put(s, mergedVars);
				if(related!=null){
					mergedVars.addAll(related);
					mergedFactor.addAll(var2Factor.get(related));
					var2Factor.remove(related);
				}
			}
		}
		
		
		var2Factor.put(mergedVars, mergedFactor);
		//Add the newVars to variables.  If it's null, it means we are scrambling variables and they
		//have already been added.
		if(newVars!=null){
			variables.addAll(newVars);
		}

		var2ConjunctCounts.put(mergedVars, new Integer(mergedFactor.size()));
	}
}
