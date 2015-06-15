package za.ac.sun.cs.green.service.bvfactorizer.resources;

import java.util.HashSet;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.SortedSet;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.ArrayVariable;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.resources.IdentityHashSet;
import za.ac.sun.cs.green.resources.HashSetMap;

public class UndeterminedArrayMerger {

	public static void mergeNecessary(Green green, HashSetMap<SelectStore> var2Vars, Map<IdentityHashSet<SelectStore>, SortedSet<Expression>> var2Factor, Set<SelectStore> variables, Map<IdentityHashSet<SelectStore>, Integer> var2ConjunctCounts, ArrayAccesses arrayAccesses, Properties smashProperties){
		//Create an ordering to examine the constraints in a manner that decreases their possible equalities by examining in a bottom up fashing
		if(smashProperties.getProperty("smash_factors", "no").equalsIgnoreCase("no")){
			mergeTraditional(var2Vars, var2Factor, variables, var2ConjunctCounts, arrayAccesses);
			return;
		}
		
		// The decision here is whether to merge all symbolic accesses into a single factor or whether
		// to try and split them.  For example, given two different factors, one of which contains arr[x]
		// and the other of which contains arr[x+1], merge would immediately just stick them into the same
		// factor which no_merge would use the SMT solver to see if they can be separated.  Based on some
		// initial measurements, it seems that two symbolic accesses of the same array will almost always
		// end up in the same factor in the end.
		if(smashProperties.getProperty("merge_symbolic_accesses", "merge").equalsIgnoreCase("merge")){
			mergeAllSymbolicAccesses(var2Vars, var2Factor, variables, var2ConjunctCounts, arrayAccesses);
		}else if(smashProperties.getProperty("merge_symbolic_accesses").equalsIgnoreCase("no_merge")){
			//Continue along your merry way and don't merge anything
		}else{
			throw new java.lang.RuntimeException("Infeasible option for merge_symbolic_immediately: {merge,no_merge}");
		}
		
		// The decision here is what to do now that we have departed from the traditional "safe" way of
		// merging.  On the one hand, we can try to prove that certain parts of a symbolic array could
		// never affect other parts of that array.  If this can be proven, that we might not need to
		// combine two factors that would usually be combined.  The other possibility is that we don't
		// check at all whether the pieces need to be merged and simply assume that they are independent.
		// This is unsafe, because things that are UNSAT can be reported as SAT.
		if(smashProperties.getProperty("smash_factors").equals("smash_and_merge_necessary")){
			mergeAllProvablyDependentFactors(green, var2Vars, var2Factor, variables, var2ConjunctCounts, arrayAccesses);
			return;
		}else if(smashProperties.getProperty("smash_factors").equals("smash_dont_merge_experimental")){
			// Only go into the OptimisticSplitter to see if want to merge symbolic accesses to the same array.
			// Data has shown these will almost ALWAYS end up in the same factor.  All other small pieces will
			// remain separate.
			return;
		}else{
			throw new java.lang.RuntimeException();
		}
	}
	
	// This merge is the traditional way of doing things.  Essentially, if there is any access to a symbolic
	// array, then every access to that array should be grouped into a single factor.
	private static void mergeTraditional(HashSetMap<SelectStore> var2Vars, Map<IdentityHashSet<SelectStore>, SortedSet<Expression>> var2Factor, Set<SelectStore> variables, Map<IdentityHashSet<SelectStore>, Integer> var2ConjunctCounts, ArrayAccesses arrayAccesses){
		for(SelectStore s: variables){
			//If that array is the first one that accesses an array in an
			//undetermined way, ie. has a variable access.
			if(arrayAccesses.causeCollapse(s)){
				Set<SelectStore> mergeVar = arrayAccesses.getAssociatedSelects(s);
				BVFactorHelper.merge(var2Vars, var2Factor, variables, var2ConjunctCounts, mergeVar, null, null);
			}
		}
	}
	
	// This function merges all factors that contain symbolic accesses to the same array into
	// a single factor.  For example, if one factor had arr[x] and another had arr[x+1], these
	// two would be merged into a single factor containing both without any SMT computation.
	private static void mergeAllSymbolicAccesses(HashSetMap<SelectStore> var2Vars, Map<IdentityHashSet<SelectStore>, SortedSet<Expression>> var2Factor, Set<SelectStore> variables, Map<IdentityHashSet<SelectStore>, Integer> var2ConjunctCounts, ArrayAccesses arrayAccesses) {
		//This set makes sure we don't double check an array
		Set<ArrayVariable> handled = new HashSet<ArrayVariable>();
		
		for(SelectStore s : variables){
			if(! handled.contains(s.getArrayAccessed()) && !s.dealsOnlyWithConstants()){
				//Get all variables that access the same array "s" does
				Set<SelectStore> possibleMergeVar = arrayAccesses.getAssociatedSelects(s);
				
				//Create an iterative set to run through all variables not in the same factor as "s"
				Set<SelectStore> copy = new HashSet<SelectStore>();
				copy.addAll(possibleMergeVar);
				copy.removeAll(var2Vars.getValue(s));

				Set<SelectStore> mustMergeVar = new HashSet<SelectStore>();
				for(SelectStore ss : copy){
					if(! ss.dealsOnlyWithConstants()){
						mustMergeVar.add(ss);
					}
				}
				
				//Only if we have found factors OTHER than the one affiliated with "s" do we need to merge
				if(mustMergeVar.size() > 0){
					mustMergeVar.add(s);
					BVFactorHelper.merge(var2Vars, var2Factor, variables, var2ConjunctCounts, mustMergeVar, null, null);
				}
				
				//Don't want to repeat looking at that variable
				handled.add(s.getArrayAccessed());
			}
		}
	}
	
	public static void mergeAllProvablyDependentFactors(Green mg, HashSetMap<SelectStore> var2Vars, Map<IdentityHashSet<SelectStore>, SortedSet<Expression>> var2Factor, Set<SelectStore> variables, Map<IdentityHashSet<SelectStore>, Integer> var2ConjunctCounts, ArrayAccesses arrayAccesses){
		for(SelectStore s : variables){
			if(! s.dealsOnlyWithConstants()){
				Set<SelectStore> mergeVar = arrayAccesses.getAssociatedSelects(s);

				Set<SelectStore> copy = new HashSet<SelectStore>();
				copy.addAll(mergeVar);
				copy.removeAll(var2Vars.getValue(s));

				Set<SelectStore> newMergeVar = new HashSet<SelectStore>();
				newMergeVar.add(s);
				for(SelectStore ss : copy){
					if(! inSameFactor(var2Vars, ss, s) && couldShareAccess(mg, var2Vars, var2Factor, ss, s)){
						newMergeVar.add(ss);
					}
				}

				BVFactorHelper.merge(var2Vars, var2Factor, variables, var2ConjunctCounts, newMergeVar, null, null);
			}
		}
	}
	
	private static boolean inSameFactor(HashSetMap<SelectStore> var2Vars, SelectStore ss, SelectStore collapsing) {
		Set<SelectStore> sStores= var2Vars.getValue(collapsing);
		return sStores.contains(ss);
	}

	private static boolean couldShareAccess(Green green, HashSetMap<SelectStore> var2Vars, Map<IdentityHashSet<SelectStore>,SortedSet<Expression>> var2Factor, SelectStore ss, SelectStore collapsing) {
		Expression first = ss.getIndex();
		Expression second = collapsing.getIndex();

		Expression newExpression = new Operation(Operation.Operator.EQ, first, second);

		//First check whether the two array accesses could ever be equal
		Instance instance = new Instance(green, null, newExpression);
		boolean possible = (Boolean) instance.request("non_recursive");
		if(!possible){
			System.out.println("We were able to factor something 1");
			return false;
		}else{
			//Next, add as much pertinent information as possible to help constrain the indices
			Set<SelectStore> collapsingStores= var2Vars.getValue(collapsing);
			Set<Expression> collapsingExpressions = var2Factor.get(collapsingStores);
			for(Expression sss : collapsingExpressions){
				newExpression = new Operation(Operation.Operator.AND, newExpression, sss);
			}

			/*
			CANNOT DO THIS, leads to unsat things being treated as sat.
			Set<SelectStore> ssStores= var2Vars.getValue(ss);
			Set<Expression> ssExpressions = var2Factor.get(ssStores);
			for(Expression sss : ssExpressions){
				newExpression = new Operation(Operation.Operator.AND, newExpression, sss);
			}
			 */
			instance = new Instance(green, null, newExpression);
			possible = (Boolean) instance.request("non_recursive");
			if(possible){
				return true;
			}else{
				System.out.println("We were able to factor something 2");
				return false;
			}
		}
	}
}
