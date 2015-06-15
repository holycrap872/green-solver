package za.ac.sun.cs.green;

public class Constants {
	
	public static final String TOOL_KEY = "tool";
	public static final String PATH_KEY = "path";
	public static final String PROGRAM_KEY = "program";
	public static final String DATABASE_KEY = "database";
	public static final String TABLE_SUFFIX_KEY = "table_suffix";
	public static final String URL_KEY = "url";
	public static final String USERNAME_KEY = "username";
	public static final String PASSWORLD_KEY = "password";
		
	//either memory or sql
	public static final String STORAGE_TYPE_KEY = "storage_type";
		public static final String MEMORY = "memory";
		public static final String SQL = "sql";
	
	
	
	public static final String SMASH_FACTORS_KEY = "smash_factors";
		//either smash, collapse, or none (none means we don't )
		public static final String SMASH_AND_MERGE_NECESSARY = "smash_and_merge_necessary";
		public static final String COLLAPSE_ALL_UNDETERMINED = "collapse_all_undetermined";
		public static final String SMASH_AND_DONT_MERGE_UNSAFE = "smash_and_dont_merge_unsafe";


	//Whether to merge the symbolic pieces without even testing whether they could access each other
	//(Data has shown they always send up merging anyways.
	public static final String MERGE_SYMBOLIC_ACCESSES_IMMEDIATELY_KEY = "merge_symbolic_accesses_immediately";
		public static final String NO_MERGE = "no_merge";
		public static final String MERGE = "merge";

	public static final String RENAME_EXPRESSION_KEY = "rename_expression";
}
