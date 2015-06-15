package za.ac.sun.cs.green.service.bvrenamer;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import za.ac.sun.cs.green.expr.Alias;
import za.ac.sun.cs.green.expr.ArrayVariable;
import za.ac.sun.cs.green.expr.Constant;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.Visitor;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.bvfactorizer.resources.AVStack;
import za.ac.sun.cs.green.service.bvfactorizer.resources.SelectStore;


public class BVRenameExpression {
	
	/*
	 * Holds all the operations directly below the &&'s
	 */
	private ArrayList<Expression> operations;
	
	/*
	 * Holds data concerning the sets of sequences of operations
	 * leading up to specific variable
	 */
	private Map<SelectStore, VarData> varSequences;
	
	/*
	 * The newly created and renamed Expression
	 */
	private Expression renamedExpression;
	
	/*
	 * private mapping from old names to new names
	 */
	private Map<SelectStore, SelectStore> assignments;
	
	/*
	 * a set of all the arrays whose index is an expression rather 
	 * than a constant and therefore could access an unknown index.
	 */
	private Map<ArrayVariable, VarData> collapsed;
	
	
	public BVRenameExpression(){
		operations = new ArrayList<Expression>();
		varSequences = new HashMap<SelectStore, VarData>();
		renamedExpression = null;
		assignments = new HashMap<SelectStore, SelectStore>();
		collapsed = new HashMap<ArrayVariable, VarData>();
	}
	
	/*
	 * Basic algorithm
	 * 
	 * Build on operations found in Base
	 * Build on varOccurences found in Base
	 * 
	 * Create variable names based the set of operations they pass through
	 * 		This information is enough to uniquely identify the variables
	 * Hash this information and sort variables based on this hash
	 * Name variables according to the sorted order of the hash
	 * 		Since the naming is arbitrary, as long as it's done in a canonical
	 * 		way we'll be fine
	 * Sort operations according to their toString methods
	 * Return all of these expression anded together in sorted order
	 */
	public BVRenameExpression(BVRenameExpression base, Expression fresh){
		
		// Create a fake base that we'll be building on
		if(base == null){
			base = new BVRenameExpression();
		}
		
		//Create a shallow copy of the operations list
		operations = new ArrayList<Expression>(base.getOperationList());
		
		//Create a deep copy of the variableData
		varSequences = new HashMap<SelectStore, VarData>();
		Map<SelectStore, VarData> oldVarSequences = base.getVariableData();
		Map<SelectStore, SelectStore> oldAssignments = base.getVariableAssignments();
		
		for(SelectStore v: oldVarSequences.keySet()){
			VarData copy = new VarData(oldVarSequences.get(v));
			varSequences.put(oldAssignments.get(v), copy);
		}
		
		collapsed = new HashMap<ArrayVariable, VarData>();
		Map<ArrayVariable, VarData> oldScrambled =  base.collapsed;
		
		for(ArrayVariable av: oldScrambled.keySet()){
			VarData copy = new VarData(oldScrambled.get(av));
			collapsed.put(av, copy);
		}

		//The other two parameters start fresh since they are calculated solely by
		//what goes on in a single instance
		renamedExpression = null;
		assignments = new HashMap<SelectStore, SelectStore>();
				
		//Collect data on the sequences of operations leading up the variables
		Collector c  = new Collector(operations, varSequences, collapsed);
		c.explore(fresh);
		
		// Create the variable map based on these sequences
		createVariablesMap();
		
		 // Rename these variables based on this new-found mapping
		Renamer r = new Renamer(varSequences, assignments);
		
		int i = 0;
		while(i<operations.size()){
			operations.set(i,(r.explore(operations.get(i))));
			i++;
		}
		
		//  Sort the operations so they are in a canonical order
		java.util.Collections.sort(operations);
		
	}
	
	/*
	 * This function is the main accessor to the expression computed by
	 * the RenamedExpression class.  It ands together the operations 
	 * after they have been sorted, leaving them in a canonical order.
	 */
	public Expression getRenamedExpression(){
		if(renamedExpression == null){
			for (Expression e : operations) {
				renamedExpression = (renamedExpression == null) ? e : new Operation(Operation.Operator.AND, renamedExpression, e);
			}
		}
		return renamedExpression;
	}
	
	/*
	 * This function created a mapping for the variables based on the
	 * sequences of operations that lead up to them.  The list is sorted
	 * according to the 1) sorted 2) hashed values of these sequences,
	 * leaving them in a canonical form.  This sorted list is then used
	 * to name the variables in increasing numbers v0, v1, ...
	 */
	private void createVariablesMap() {
			
		ArrayList<VarData> sort = new ArrayList<VarData>();
		for(SelectStore s: varSequences.keySet()){
			if(!collapsed.containsKey(s.getArrayAccessed())){
				sort.add(varSequences.get(s));
			}
			else{
				collapsed.get(s.getArrayAccessed()).mergeVarData(varSequences.get(s));
			}
		}
		
		Collections.shuffle(sort); //Shuffle done for testing purposes to test determinism of algorithm
		Collections.sort(sort);
		int i = 0;
		
		/*
		 * For all un-collapsed array references, rename them based on the operations
		 * that reach them.  This provides a canonical naming of the variables since
		 * these paths are unique, and then sorted.
		 */
		for(VarData v: sort){
			v.setNewNameIndex("array", i);
			i++;
		}
		
		sort = new ArrayList<VarData>();
		for(VarData v: collapsed.values()){
			sort.add(v);
		}
		Collections.shuffle(sort);
		Collections.sort(sort);
		i = 0;
		
		/*
		 * For all collapsed array references, name them based on the paths that
		 * reach all of the array accesses. 
		 */
		for(VarData v: sort){
			v.setNewNameIndex("array"+i, 0);
			i++;
		}
		
	}
	
	public ArrayList<Expression> getOperationList() {
		return operations;
	}
	
	public Map<SelectStore, VarData> getVariableData(){
		return varSequences;
	}
	
	public Map<SelectStore, SelectStore> getVariableAssignments(){
		return assignments;
	}
	
	public String toString(){
		return getRenamedExpression().toString();
	}
	
	public int getNumFactors() {
		return operations.size();
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
		 * List of all of the operations in the conjunct
		 */
		private ArrayList<Expression> operations = null;
		
		/**
		 * A map from each variable to the number of times
		 * it occurs
		 */
		private Map<SelectStore, VarData> varSequences = null;
		
		/*
		 * Keeps track of all instances where the arrayvariable's index is a variable,
		 * meaning that it could reference any part of that array.  We have to be
		 * careful of this and group all references to that array together.
		 */
		private Map<ArrayVariable, VarData> collapsed = null;
		
		/*
		 * A stack that keeps track of the current operation sequence we are exploring,
		 * allowing us to pull this information and associate it with every array variable
		 * we encounter. 
		 */
		private Stack<String> operationSequence = null;
		
		/*
		 * A stack keeping track of how deep into a particular conjunct we are (not including
		 * the top level &&'s)
		 */
		private Stack<Integer> depth = null;
		
		/*
		 * Keeps track of the last arrayvariable seen while exploring an expression
		 * This is useful upon encountering stores or selects since klee can represent
		 * multiple stores as store( store( store( array, index value), index, value) index, value)
		 * 
		 * For a more indepth explanation see BVFactorizeExpression.
		 */
		private AVStack store = null;
		
		/*
		 * For operations where the position of the arguments matter (ex. x >= y
		 * matters but x == y doesn't) we want to encode this information, along
		 * with the string of the operation, to the VarData object. This
		 * eliminate instances such as v1 > v2 where v1 hashes to the same value
		 * as v2. Basically, want to encode not only the operations that they
		 * variables are under, but their position under these operations when
		 * it matters.
		 * 
		 * In order to do this, we use a stack to hold this information, the
		 * previsit pushing a 0op on the stack, the next visit popping that and
		 * pushing a 1op on the stack.
		 * 
		 * Even though two variables may hash to the same value (for example,
		 * (x!=y+1)&&(x==y)), this doesn't destroy the safety of the operation,
		 * ie. mean that a hit is not actually a hit. Instead it means that we
		 * miss a potential hit. This is something to work on in the future.
		 */

		public Collector(ArrayList<Expression> operations, Map<SelectStore, VarData> varSequences, Map<ArrayVariable, VarData> scrambled) {
			this.operations = operations;
			this.varSequences = varSequences;
			this.collapsed = scrambled;
			this.depth = new Stack<Integer>();
			operationSequence = new Stack<String>();
			operationSequence.push("");	//Do this so don't have to worry about empty stack errors
			
			//position = new Stack<Integer>();
			//position.push(0);
			
			store = new AVStack();
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
				e.printStackTrace();
			}
		}
		
		@Override
		/*
		 * Aliases are handled differently from most operations.  This is because we
		 * don't want to analyze them twice since they will contain the same information
		 * each time.  Therefore, if they have been analyzed before then just take the
		 * operations that have been previously been computed and add them to the store
		 * and to the varsequences.
		 */
		public void preVisit(Alias a){
			if(!a.hasRenamerInformation()){
				a.exploreSubexpression(true);
				a.setRenamerVisitorState(store, operationSequence, varSequences, collapsed);
				
				operationSequence = new Stack<String>();
				operationSequence.push("");
				
				varSequences = new HashMap<SelectStore, VarData>();
				
				collapsed = new HashMap<ArrayVariable, VarData>();
				
				store = new AVStack();
				
				//Assuming it is impossible for operations to be affected in an alias
				//since an alias will NEVER be an entire constraint in itself, just a part
				//to some other constraints
				
			}
		}
		
		@Override
		public void postVisit(Alias alias){
			if(!alias.hasRenamerInformation()){
				alias.setRenamerAliasInformation(varSequences, collapsed);
				
				operationSequence = alias.getRenamedOperationSequence();
				varSequences = alias.getRenamedVarSequences();
				collapsed = alias.getRenamedScrambled();
				store = alias.getRenamerStateStack();
				
				alias.exploreSubexpression(false);
			}
			store.stickOntoEnd(alias.getFactorizerAliasStack());
			updateVarSequences(operationSequence, varSequences, collapsed, alias);
		}
		

		/*
		 * Should combine the operations in aliasVarsequences to the uppermost part of operationsequence
		 * and add it to varSeqeuences.
		 * 
		 * For example
		 * operationSequence.peek =(CONCATCONCAT+==
		 * should add this bit to the beginning of every vardata piece in aliasVarSequence and add combined
		 * thing to appropriate Vardata in VarSequence
		 */
		private void updateVarSequences(Stack<String> operationSequence, Map<SelectStore, VarData> varSequences, Map<ArrayVariable, VarData> scrambled, Alias a) {
			handleCollapse(scrambled, a.getRenamedAliasScrambled(), operationSequence.peek());
			
			handleVarSequences(scrambled, varSequences, a.getRenamedAliasVarSequences(), operationSequence.peek());
		}
		
		/*
		 * Does two things
		 * 1) If the element of scramble is the first time it was seen in the scrambledParent, adds it.
		 * 		In this case it has to go through all the selects in varSequences in remove them since
		 * 		it is the first time
		 * 2) Otherwise, just joins the information in the two of them.
		 */
		private void handleCollapse(Map<ArrayVariable, VarData> collapsedParent, Map<ArrayVariable, VarData> scrambledAlias, String prepend){
			//By definition, those in 
			for(ArrayVariable av: scrambledAlias.keySet()){
				VarData newV = new VarData(scrambledAlias.get(av));
				newV.prepend(prepend);
				VarData v = collapsedParent.get(av);
				if(v==null){
					collapsedParent.put(av, newV);
				}else{
					v.mergeVarData(newV);
				}
			}
		}
		
		private void handleVarSequences(Map<ArrayVariable, VarData> scrambledParent, Map<SelectStore, VarData> varSequencesParent, Map<SelectStore, VarData> varSequencesAlias, String prepend){
			for(SelectStore s: varSequencesAlias.keySet()){
				VarData newV = new VarData(varSequencesAlias.get(s));
				newV.prepend(prepend);
				if(scrambledParent.containsKey(s.getArrayAccessed())){
					scrambledParent.get(s.getArrayAccessed()).mergeVarData(newV);
				}else{
					VarData v = varSequencesParent.get(s);
					if(v==null){
						varSequencesParent.put(s, newV);
					}else{
						v.mergeVarData(newV);
					}
				}
			}
		}

		
		@Override
		public void postVisit(Variable variable){
			if(variable instanceof ArrayVariable){
				store.push((ArrayVariable)variable);
			}else{
				store.push(store.peek());
			}
		}
		
		@Override
		public void postVisit(Constant constant){
			store.push(store.peek());
		}

		/*
		 * 1) Flips LE/LT -> GE/GT
		 * 2) adds the string of the operation to the stack so it can be used
		 * to uniquely identify variables
		 */
		@Override
		public void preVisit(Operation operation) {
				
			Operation.Operator op = ((Operation) operation).getOperator();
			
			if(op!= Operation.Operator.AND){

				//Will eventually flip these operators when we get the ordering we want
				if(op==Operation.Operator.LT){
					op = Operation.Operator.GT;
				}else if(op==Operation.Operator.LE){
					op = Operation.Operator.GE;
				}else if(op==Operation.Operator.BVULT){
					op = Operation.Operator.BVUGT;
				}else if(op==Operation.Operator.BVSLT){
					op = Operation.Operator.BVSGT;
				}else if(op==Operation.Operator.BVULE){
					op = Operation.Operator.BVUGE;
				}else if(op==Operation.Operator.BVSLE){
					op = Operation.Operator.BVSGE;
				}

				String s = op.toString();
				operationSequence.push(s+operationSequence.peek());

				//When depth is 0, then we know we are at the upper most part of a constraint
				if(op.isComparator()){
					if(depth.isEmpty()){
						operations.add(operation);
					}
					depth.push(new Integer(1));
				}
			}
		}

		@Override
		/*
		 * Removes the string containing this operation from the stack
		 */
		public void postVisit(Operation operation){
			Operation.Operator op = ((Operation) operation).getOperator();

			//If it's a store operation
			if(op == Operation.Operator.SELECT || op == Operation.Operator.STORE){
				
				Expression index = operation.getOperand(1);
				Expression directAV = operation.getOperand(0);
				
				ArrayVariable prospective = getArrayStoreSelect(store, operation);
				
				SelectStore s = null;
				//Still care if directly dealing with array variable since if we're not
				//all of the information about it's path is already contained in operationSequence
				if(directAV instanceof ArrayVariable){
					s = new SelectStore((ArrayVariable)directAV, index);
				}else{
					s = new SelectStore(prospective, index);
				}

				//If dealing directly with an array variable and it's constant and it hasn't been scrambled yet
				//directAV is important b/c we don't want to add information to vardata unless we're directly dealing with variable
				//constant is important since we know it doesn't cause a scramble
				//That combined with the fact it's not a part of a scramble means we don't need to scramble
				if(s.dealsOnlyWithConstants()){
					if(directAV instanceof ArrayVariable){
						if(!collapsed.containsKey(directAV)){
							VarData v = varSequences.get(s);
							if(v==null){
								v = new VarData((ArrayVariable)directAV, index);
								varSequences.put(s, v);
							}
							v.addOperationSequence(operationSequence.peek());
						}else{
							//If constant, directly touching array, but a part of scramble
							//then add to pre-existing scramble
							VarData v = collapsed.get(s.getArrayAccessed());
							v.addOperationSequence(operationSequence.peek());
						}
					}else{
						//Not directly dealing with array
						//Can't add information by adding to scramble
					}

				}else{
					//We know that the index is not constant.  The two options are
					//1) It is a part of a scramble
					//2) It should cause a scramble
					
					VarData v = collapsed.get(s.getArrayAccessed());
					//If not a part of scrambled yet, means we have to merge all VarData related to it.
					if(v==null){
						v = new VarData(s.getArrayAccessed(), index);
						//Will clean up varSequences later
						collapsed.put(s.getArrayAccessed(), v);
					}
					
					//Only add ourself, however, if directly dealing with variable 
					if(directAV instanceof ArrayVariable){
						v.addOperationSequence(operationSequence.peek());
					}
				}

				//Otherwise just remove the correct number of ArrayVariables seen and add the most recent one
			}else{
				storeUpdate(store, op);
			}

			//Added only non AND operations above
			if(op!=Operation.Operator.AND){
				operationSequence.pop();
				
				//Do this to keep track of when we reach the uppermost comparator
				if (op.isComparator()) {
					depth.pop();
				}	
			}
		}

	}
	
	private void storeUpdate(AVStack store, Operation.Operator op){
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

	/*
	 * Based on the new mapping calculated by previous steps, creates
	 * a new expression with variables adopting these new names.
	 */
	private class Renamer extends Visitor {
		
		/**
		 * A map from each variable to the number of times
		 * it occurs
		 */
		private Map<SelectStore, VarData> varSequences;
		
		private Stack<Expression> stack;
		
		private Map<SelectStore, SelectStore> assignments;
		

		/**
		 * Constructor that sets the two mappings that the collector builds.
		 * 
		 * @param conjunct2Vars
		 *            a map from conjuncts to the variables they contain
		 * @param var2Conjuncts
		 *            a map from the variables to the conjuncts in which they
		 *            appear
		 */
		public Renamer(Map<SelectStore, VarData> varSequences, Map<SelectStore, SelectStore> assignments) {
			this.varSequences = varSequences;
			stack = new Stack<Expression>();
			this.assignments = assignments;
		}

		/**
		 * Explores the expression by setting the default conjunct and then
		 * visiting the expression.
		 * 
		 * @param expression
		 *            the expression to explore
		 */
		public Expression explore(Expression expression) {
			try {
				expression.accept(this);
				return stack.pop();
			} catch (VisitorException e) {
				e.printStackTrace();
				return null;
			}
		}
		
		@Override
		public void postVisit(Operation operation) {
			int arity = operation.getOperator().getArity();
			Operation.Operator op = ((Operation) operation).getOperator();
			Expression operands[] = new Expression[arity];
			
			if(op == Operation.Operator.SELECT){
				Expression index = stack.pop();	
				Expression av = stack.pop();
				
				//If directly associated with variable
				if(av instanceof ArrayVariable){
					
					//If scrambled, get new array name but keep old index (since one by defn will be an expression)
					if(collapsed.containsKey(av)){
						operands[0] = collapsed.get(av).getNewName();
						operands[1] = index;
						
					//Otherwise, create a select to get information about that particular access
					}else{
						SelectStore key = new SelectStore((ArrayVariable)av, index);
						SelectStore newName = assignments.get(key);
						
						//If hasn't been accessed yet, create a quick mapping
						if(newName == null){
							newName = new SelectStore(varSequences.get(key).getNewName(), varSequences.get(key).getNewIndex());
							assignments.put(key, newName);
						}

						operands[0] = newName.getArrayAccessed();
						operands[1] = newName.getIndex();
					}
				}else{
					//Otherwise, don't touch
					operands[0] = av;
					operands[1] = index;
				}
			}else if(op == Operation.Operator.STORE){
				Expression value = stack.pop();
				Expression index = stack.pop();	
				Expression av = stack.pop(); //get rid of data in slot where av is

				if(av instanceof ArrayVariable){
					if(collapsed.containsKey(av)){
						operands[0] = collapsed.get(av).getNewName();
						operands[1] = index;
						operands[2] = value;
					}else{
						SelectStore key = new SelectStore((ArrayVariable)av, index);
						SelectStore newName = assignments.get(key);
						if(newName == null){
							newName = new SelectStore(varSequences.get(key).getNewName(), varSequences.get(key).getNewIndex());
							assignments.put(key, newName);
						}

						operands[0] = newName.getArrayAccessed();
						operands[1] = newName.getIndex();
						operands[2] = value;
					}
				}else{
					operands[0] = av;
					operands[1] = index;
					operands[2] = value;
				}
			}else if(op == Operation.Operator.LT){
				for (int i = 0; i < arity; i++) {
					operands[i] = stack.pop();
				}
				op = Operation.Operator.GT;
			}else if(op == Operation.Operator.LE){
				for (int i = 0; i < arity; i++) {
					operands[i] = stack.pop();
				}
				op = Operation.Operator.GE;
			}else if(op == Operation.Operator.BVULT){
				for (int i = 0; i < arity; i++) {
					operands[i] = stack.pop();
				}
				op = Operation.Operator.BVUGT;
			}else if(op == Operation.Operator.BVSLT){
				for (int i = 0; i < arity; i++) {
					operands[i] = stack.pop();
				}
				op = Operation.Operator.BVSGT;
				
			}else if(op == Operation.Operator.BVULE){
				for (int i = 0; i < arity; i++) {
					operands[i] = stack.pop();
				}
				op = Operation.Operator.BVUGE;
			}else if(op == Operation.Operator.BVSLE){
				for (int i = 0; i < arity; i++) {
					operands[i] = stack.pop();
				}
				op = Operation.Operator.BVSGE;
			}else if ((op == Operation.Operator.EQ) || (op == Operation.Operator.NE) || 
					(op == Operation.Operator.STRINGEQUALS) || (op == Operation.Operator.EQUALSIGNORECASE) ||
					(op == Operation.Operator.NOTEQUALSIGNORECASE)||(op == Operation.Operator.STRINGNOTEQUALS)) {
				Expression left = stack.pop();
				Expression right = stack.pop();
				
				if(left.compareTo(right)>0){
					operands[0]=left;
					operands[1]=right;
				}else{
					operands[0]=right;
					operands[1]=left;
				}
				
				stack.push(new Operation(op, operands));
				
				/*
				 * Clear out the string buffers stored in sub expressions since they
				 * won't be used again.  This has to be done because the "compareTo"
				 * operation indirectly calls the toString method, which makes the 
				 * operations save a duplicate and unneeded string buffer.
				 */
				stack.peek().toString();
				if(operands[0] instanceof Operation){
					((Operation)operands[0]).clearString();
				}
				if(operands[1] instanceof Operation){
					((Operation)operands[1]).clearString();
				}
				
				//Short circuit b/c of special 
				return;

			}else{
				//Go backwards (X..1,0) since we aren't swtiching the order of any of these.
				for (int i = arity; i > 0; i--) {
					operands[i - 1] = stack.pop();
				}
			}
			stack.push(new Operation(op, operands));
			
		}
		
		@Override
		public void postVisit(Constant constant) {
			stack.push(constant);
		}
		
		@Override
		public void postVisit(Variable variable) {
			stack.push(variable);
		}
		
		@Override
		public void preVisit(Alias a){		
			a.exploreSubexpression(true);
		}
	}

}
