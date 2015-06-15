package za.ac.sun.cs.green.service.bvfactorizer.resources;

import za.ac.sun.cs.green.expr.ArrayVariable;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.BitVectorConstant;

/*
 * This class represents a select/store operation.  It is meant to
 * represent array accesses and their possible effects.  For example
 * array[INTEGER] is an access that is isolated to a single element
 * of the array.  array[VARIABLE], however, is an operation that can
 * not be factorized, and will draw in all other operations associated
 * with the particular array.
 */
public class SelectStore{
	private final ArrayVariable access;
	private final Expression index;

	private final boolean dealsExclusivelyWithConstants;
	
	private String toString;
	private int hashCode;
	private boolean hashCodeCalculated;
	
	public SelectStore(ArrayVariable access, Expression index){
		this.access = access;
		this.index = index;

		if(index instanceof BitVectorConstant){
			this.dealsExclusivelyWithConstants = true;

		}else{
			this.dealsExclusivelyWithConstants = false;
		}

		toString = null;
		hashCodeCalculated = false;
	}
	
	public ArrayVariable getArrayAccessed(){
		return this.access;
	}
	
	public Expression getIndex(){
		return this.index;
	}
	
	/*
	 * Tells whether there is a chance for multiple elements to be
	 * accessed.  In this case we would likely need some type of solver
	 * to determine which specific ones are accessed.
	 */
	public boolean dealsOnlyWithConstants(){
		return this.dealsExclusivelyWithConstants;
	}
	
	@Override
	public int hashCode(){
		if(!hashCodeCalculated){
			hashCode = toString().hashCode();
			hashCodeCalculated = true;
		}
		return hashCode;
	}
	
	@Override
	public String toString(){
		if(toString == null){
			toString = access.toString()+"["+index.toString()+"]";
		}
		return toString;
	}

	@Override
	public boolean equals(Object o){
		if(o instanceof SelectStore){
			if(o.toString().equals(this.toString())){
				return true;
			}
		}
		return false;
	}
	
	public boolean sameArray(SelectStore s){
		if(s.access.equals(this.access)){
			return true;
		}
		return false;
	}
}
