package za.ac.sun.cs.green.service.bvfactorizer.resources;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import za.ac.sun.cs.green.expr.ArrayVariable;

public class ArrayAccesses {
	
	private static int STARTSIZE = 50;
	
	private Map<ArrayVariable, Set<SelectStore>> array2accesses;
	
	private Set<ArrayVariable> collapse;
	
	public ArrayAccesses(){
		array2accesses = new HashMap<ArrayVariable, Set<SelectStore>>(STARTSIZE);
		collapse = new HashSet<ArrayVariable>();
	}
	
	public ArrayAccesses(ArrayAccesses old){
		collapse = new HashSet<ArrayVariable>(old.collapse);
		array2accesses = new HashMap<ArrayVariable, Set<SelectStore>>();
		for(Object obj: old.array2accesses.keySet()){
			ArrayVariable av = (ArrayVariable)obj;
			array2accesses.put(av, old.array2accesses.get(av));
		}
	}
	
	public void insertAccess(SelectStore s){
		//See if this array has been accessed yet
		Set<SelectStore> access = array2accesses.get(s.getArrayAccessed());
		if(access == null){
			//If it hasn't create a new set
			access = new HashSet<SelectStore>();
			array2accesses.put(s.getArrayAccessed(), access);
		}
		//Add this access to set
		access.add(s);
	}

	/*
	 * When given a select statement, this method adds that statement
	 * to the set of statements that are associated with a particular array.
	 * It then returns false or true depending on whether or not this
	 * new value is the first one associated with a particular array
	 * with a non constant index.  A return of true
	 * means that all constraints associated with select statements calling
	 * a particular array should be merged.
	 */
	public boolean causeCollapse(SelectStore s){
		//If it's constant, couldn't possible cause a scramble
		if(s.dealsOnlyWithConstants()){
			return false;
		}else{
			//Also if the array has already been scrambled, then this couldn't be a cause
			if(collapse.contains(s.getArrayAccessed())){
				return false;
			}else{
				collapse.add(s.getArrayAccessed());
				return true;
			}
		}
	}
	
	public Set<SelectStore> getAssociatedSelects(SelectStore s){
		return array2accesses.get(s.getArrayAccessed());
	}
}
