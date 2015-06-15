package za.ac.sun.cs.green.resources;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


/*
 * Creates a mapping for each individual variable in a set, to that set
 * 
 * For example for the set {1,2,3} 1->{1,2,3}, 2->{1,2,3}, 3->{1,2,3}
 */
public class HashSetMap<T> {
	
	private static int STARTSIZE = 500;
	
	private Map<T, Set<T>> var2Vars;
	
	public HashSetMap(){
		var2Vars = new HashMap<T, Set<T>>(STARTSIZE);
	}
	
	public HashSetMap(HashSetMap<T> other){
		var2Vars = new HashMap<T, Set<T>>(STARTSIZE);
		for(T s: other.getKeySet()){
			var2Vars.put(s, new HashSet<T>(other.getValue(s)));
		}
	}
	
	/*
	 * Does one of two things
	 * 1) If variable wasn't in map yet, puts it in with a pointer to the related variables and returns null
	 * 2) If it is in, updates all of the variables that it was previously pointing to to point to this
	 * new relatedVariables set. 
	 */
	public Set<T> put(T variable, Set<T> relatedVariables){
		Set<T> ret = var2Vars.put(variable, relatedVariables);
		if(ret == null){
			return null;
		}else{
			for(T s: ret){
				var2Vars.put(s, relatedVariables);
			}
		}
		return ret;
	}
	
	public Set<T> getKeySet(){
		return var2Vars.keySet();
	}
	
	public Set<T> getValue(T key){
		return var2Vars.get(key);
	}

	public void addAll(Set<T> vars) {
		for(T s: vars){
			var2Vars.put(s, vars);
		}	
	}
	
	public Set<Set<T>> getValues(){
		Set<Set<T>> ret = new HashSet<Set<T>>();
		for(Set<T> set : var2Vars.values()){
			Set<T> newSet = new HashSet<T>();
			newSet.addAll(set);
			ret.add(newSet);
		}
		
		return ret;
	}

}
