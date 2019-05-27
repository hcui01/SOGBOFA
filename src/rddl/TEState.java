/**
 * RDDL: Main state representation and transition function 
 *       computation methods; this class requires everything
 *       to simulate a RDDL domain instance.
 * 
 * @author Scott Sanner (ssanner@gmail.com)
 * @version 10/10/10
 *
 **/

package rddl;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.Map.Entry;

import org.apache.commons.math3.random.RandomDataGenerator;

import rddl.RDDL.AGG_EXPR;
import rddl.RDDL.BOOL_EXPR;
import rddl.RDDL.COMP_EXPR;
import rddl.RDDL.CONN_EXPR;
import rddl.RDDL.CPF_DEF;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.ENUM_VAL;
import rddl.RDDL.EXPR;
import rddl.RDDL.LCONST;
import rddl.RDDL.LCONST_TYPE_DEF;
import rddl.RDDL.LTERM;
import rddl.RDDL.LTYPED_VAR;
import rddl.RDDL.LVAR;
import rddl.RDDL.OBJECTS_DEF;
import rddl.RDDL.OBJECT_TYPE_DEF;
import rddl.RDDL.PVARIABLE_ACTION_DEF;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVARIABLE_INTERM_DEF;
import rddl.RDDL.PVARIABLE_OBS_DEF;
import rddl.RDDL.PVARIABLE_STATE_DEF;
import rddl.RDDL.PVARIABLE_WITH_DEFAULT_DEF;
import rddl.RDDL.PVAR_EXPR;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import rddl.RDDL.QUANT_EXPR;
import rddl.RDDL.OPER_EXPR;
import rddl.RDDL.STRUCT_TYPE_DEF;
import rddl.RDDL.STRUCT_VAL;
import rddl.RDDL.TYPE_DEF;
import rddl.RDDL.TYPE_NAME;
import rddl.policy.Policy;
import rddl.viz.TERDDL2Graph;
import util.Pair;

public class TEState {
	public final static boolean DISPLAY_UPDATES = false;
	public final static int UNDEFINED = 0;
	public final static int STATE     = 1;
	public final static int NONFLUENT = 2;
	public final static int ACTION    = 3;
	public final static int INTERM    = 4;
	public final static int OBSERV    = 5;
	
	// PVariable definitions
	public HashMap<PVAR_NAME,PVARIABLE_DEF> _hmPVariables;
	
	// Type definitions
	public HashMap<TYPE_NAME,TYPE_DEF> _hmTypes;
	
	// CPF definitions
	public HashMap<PVAR_NAME,CPF_DEF> _hmCPFs;
	
	// Object ID lookup... we use IntArrays because hashing and comparison
	// operations will be much more efficient this way than with Strings.
	public HashMap<TYPE_NAME,ArrayList<LCONST>> _hmObject2Consts;
	
	// Lists of variable names
	public ArrayList<PVAR_NAME> _alStateNames = new ArrayList<PVAR_NAME>();
	public ArrayList<PVAR_NAME> _alActionNames = new ArrayList<PVAR_NAME>();
	public TreeMap<Pair,PVAR_NAME> _tmIntermNames = new TreeMap<Pair,PVAR_NAME>();
	public ArrayList<PVAR_NAME> _alIntermNames = new ArrayList<PVAR_NAME>();
	public ArrayList<PVAR_NAME> _alObservNames = new ArrayList<PVAR_NAME>();
	public ArrayList<PVAR_NAME> _alNonFluentNames = new ArrayList<PVAR_NAME>();
	public HashMap<String,ArrayList<PVAR_NAME>> _hmTypeMap = new HashMap<String,ArrayList<PVAR_NAME>>();
	
	// String -> (IntArray -> Object)
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>> _state;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>> _nonfluents;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>> _actions;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>> _interm;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>> _observ;

	// Orderings for evaluating derived and intermediate fluents
	public ArrayList<Pair> _alIntermGfluentOrdering  = new ArrayList<Pair>();
	public ArrayList<Pair> _alDerivedGfluentOrdering = new ArrayList<Pair>();

	// Constraints
	//public ArrayList<BOOL_EXPR> _alConstraints;
	public ArrayList<BOOL_EXPR> _alActionPreconditions;
	public ArrayList<BOOL_EXPR> _alStateInvariants;
	public EXPR _reward;
	public int _nMaxNondefActions = -1;
	

	
	//record sum constraints
	//need to apply the projection on each step
	//based on the sum constraints
	
	// Underlying graphical model
	public TERDDL2Graph _r2g = null;

	public Object clone() {
		Object o = null;
		try {
			o = (EState) super.clone();
		} catch (CloneNotSupportedException e) {
			System.out.println(e.toString());
		}
		return o;
	} 
	
	// Temporarily holds next state while it is being computed
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>> _nextState;
	
	// translat object to double
		// only supports int, bool
		public static double getDouble(Object o) throws EvalException {
			if (o instanceof ENUM_VAL) {
				throw new EvalException("enum not supported");
			}
			if (o instanceof Boolean) {
				return (Boolean) o ? 1.0 : 0.0;
			} else if (o instanceof Integer) {
				return Double.parseDouble(o.toString());
			} else{
				if(o instanceof Double || o instanceof Float){
					return (Double)o;
				}
				else{
					throw new EvalException("do not support this type: " + o);
				}
			}
		}
	
	// translat object to TExp
	// only supports int, bool, long, cdouble
	public static TreeExp toTExp(Object o, TreeExp father) throws EvalException {
		if (o instanceof TreeExp) {
			return (TreeExp) o;
		}
		if (o instanceof ENUM_VAL) {
			throw new EvalException("enum not supported");
		}
		

		double theVal;
		if (o instanceof Boolean) {
			theVal = (Boolean) o ? 1.0 : 0.0;
		} else if (o instanceof Integer) {
			theVal = Double.valueOf(o.toString());
		} else {

			theVal = (Double) o;
		}
		return TreeExp.BuildNewTreeExp(getDouble(theVal), father);
	}
	
	public boolean IfSame(TEState newS){
		boolean ifSame = true;
		Iterator thisIterator = _state.entrySet().iterator(); 
		while (thisIterator.hasNext()) { 
		    Map.Entry entry = (Map.Entry) thisIterator.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Object> val = (HashMap<ArrayList<LCONST>, Object>)entry.getValue(); 
		    Iterator inner = val.entrySet().iterator();
		    while (inner.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    Object theValue = entry2.getValue(); 
			    if(!newS._state.get(key).containsKey(theTerm)){
			    	ifSame = false;
			    	break;
			    }
			    if(!theValue.equals(newS._state.get(key).get(theTerm))){
			    	ifSame = false;
			    	break;
			    }
			} 
		    if(!ifSame){
		    	break;
		    }
		} 
		
		Iterator newIterator = newS._state.entrySet().iterator(); 
		while (newIterator.hasNext()) { 
		    Map.Entry entry = (Map.Entry) newIterator.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Object> val = (HashMap<ArrayList<LCONST>, Object>)entry.getValue(); 
		    Iterator inner = val.entrySet().iterator();
		    while (inner.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    Object theValue = entry2.getValue(); 
			    if(!_state.get(key).containsKey(theTerm)){
			    	ifSame = false;
			    	break;
			    }
			    if(!theValue.equals(_state.get(key).get(theTerm))){
			    	ifSame = false;
			    	break;
			    }
			} 
		    if(!ifSame){
		    	break;
		    }
		} 
		return ifSame;
	}
	
	//from normal initial state to aggregate initial state
	// only support boolean state variable now
	// partially completed; only non-default value is dealt
	public boolean InitAggState(State initS) throws EvalException {

		TreeExp node0 = TreeExp.BuildNewTreeExp(0.0, null);
		TreeExp node1 = TreeExp.BuildNewTreeExp(1.0, null);
		Iterator outer = initS._state.entrySet().iterator();
		while (outer.hasNext()) {
			Map.Entry entry = (Map.Entry) outer.next();
			PVAR_NAME key = (PVAR_NAME) entry.getKey();
			HashMap<ArrayList<LCONST>, Object> val = (HashMap<ArrayList<LCONST>, Object>) entry
					.getValue();
			Iterator inner = val.entrySet().iterator();
			HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _state.get(key);
			while (inner.hasNext()) {
				Map.Entry entry2 = (Map.Entry) inner.next();
				ArrayList<LCONST> theTerm = (ArrayList<LCONST>) entry2.getKey();
				if (Global.ifLift) {
					if (!(Boolean) entry2.getValue()) {
						pred_assign.put(theTerm, node0);
					} else {
						pred_assign.put(theTerm, node1);
					}
				} else {
					TreeExp theValue = toTExp(entry2.getValue(), null);
					pred_assign.put(theTerm, theValue);
				}
			}
		}
		Iterator outer2 = initS._nonfluents.entrySet().iterator();
		while (outer2.hasNext()) {
			Map.Entry entry = (Map.Entry) outer2.next();
			PVAR_NAME key = (PVAR_NAME) entry.getKey();
			HashMap<ArrayList<LCONST>, Object> val = (HashMap<ArrayList<LCONST>, Object>) entry
					.getValue();
			Iterator inner2 = val.entrySet().iterator();
			HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _nonfluents
					.get(key);
			while (inner2.hasNext()) {
				Map.Entry entry2 = (Map.Entry) inner2.next();
				ArrayList<LCONST> theTerm = (ArrayList<LCONST>) entry2.getKey();
				TreeExp theValue = toTExp(entry2.getValue(), null);
				pred_assign.put(theTerm, theValue);
			}
		}
		return true;

	}

	public boolean InitAggState(TEState initS) throws EvalException {
		TreeExp node0 = TreeExp.BuildNewTreeExp(0.0, null);
		TreeExp node1 = TreeExp.BuildNewTreeExp(1.0, null);
		// throw new
		// EvalException("do not support this initialization from another astate yet!");
		Iterator outer = initS._state.entrySet().iterator();
		while (outer.hasNext()) {
			Map.Entry entry = (Map.Entry) outer.next();
			PVAR_NAME key = (PVAR_NAME) entry.getKey();
			HashMap<ArrayList<LCONST>, TreeExp> val = (HashMap<ArrayList<LCONST>, TreeExp>) entry
					.getValue();
			Iterator inner = val.entrySet().iterator();
			HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _state.get(key);
			while (inner.hasNext()) {
				Map.Entry entry2 = (Map.Entry) inner.next();
				ArrayList<LCONST> theTerm = (ArrayList<LCONST>) entry2.getKey();
				if (Global.ifLift) {
					if (!(Boolean) entry2.getValue()) {
						pred_assign.put(theTerm, node0);
					} else {
						pred_assign.put(theTerm, node1);
					}
				} else {
					TreeExp theValue = toTExp(entry2.getValue(), null);
					pred_assign.put(theTerm, theValue);
				}
			}
		}
		Iterator outer2 = initS._nonfluents.entrySet().iterator();
		while (outer2.hasNext()) {
			Map.Entry entry = (Map.Entry) outer2.next();
			PVAR_NAME key = (PVAR_NAME) entry.getKey();
			HashMap<ArrayList<LCONST>, TreeExp> val = (HashMap<ArrayList<LCONST>, TreeExp>) entry
					.getValue();
			Iterator inner2 = val.entrySet().iterator();
			HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _nonfluents
					.get(key);
			while (inner2.hasNext()) {
				Map.Entry entry2 = (Map.Entry) inner2.next();
				ArrayList<LCONST> theTerm = (ArrayList<LCONST>) entry2.getKey();
				TreeExp theValue = (TreeExp) entry2.getValue();
				pred_assign.put(theTerm, theValue);
			}
		}
		return true;

	}
	
	
	
	


	public boolean InitAggState(EState initS) throws EvalException {
		
		Iterator outer = initS._state.entrySet().iterator(); 
		while (outer.hasNext()) { 
		    Map.Entry entry = (Map.Entry) outer.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Double> val = (HashMap<ArrayList<LCONST>, Double>)entry.getValue(); 
		    Iterator inner = val.entrySet().iterator();
		    HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _state.get(key);
		    while (inner.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    TreeExp theValue = toTExp((entry2.getValue()), null); 
			    pred_assign.put(theTerm, theValue);
			} 
		} 
		Iterator outer2 = initS._nonfluents.entrySet().iterator(); 
		while (outer2.hasNext()) { 
		    Map.Entry entry = (Map.Entry) outer2.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Double> val = (HashMap<ArrayList<LCONST>, Double>)entry.getValue(); 
		    Iterator inner2 = val.entrySet().iterator();
		    HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _nonfluents.get(key);
		    while (inner2.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner2.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    TreeExp theValue = toTExp(entry2.getValue(), null); 
			    pred_assign.put(theTerm, theValue);
			} 
		} 
		return true;
	}
	
	//restore astate from another astate
	//only deal with _state
	public boolean RestoreAState(TEState ori) throws EvalException{
		for(PVAR_NAME p : _alStateNames){
			HashMap<ArrayList<LCONST>, TreeExp> ori_state = ori._state.get(p);
			//HashMap<ArrayList<LCONST>, Double> ori_nextState = ori._nextState.;
			HashMap<ArrayList<LCONST>, TreeExp> des_state = _state.get(p);
			ArrayList<ArrayList<LCONST>> terms = generateAtoms(p);
			for(ArrayList<LCONST> term : terms){
				des_state.put(term, ori_state.get(term));
			}
		}
		return true;
	}
	
	public void init(State s) throws EvalException {
		
		_hmPVariables = s._hmPVariables;
		_hmTypes = s._hmTypes;
		_hmCPFs = s._hmCPFs;
		_alActionPreconditions = s._alActionPreconditions;
		_alStateInvariants = s._alStateInvariants;
		_reward = s._reward;
		_nMaxNondefActions = s._nMaxNondefActions;
		
		// Map object class name to list
		_hmObject2Consts = new HashMap<TYPE_NAME,ArrayList<LCONST>>();
		for (Map.Entry<TYPE_NAME,ArrayList<LCONST>> o2c : s._hmObject2Consts.entrySet()) {
			_hmObject2Consts.put(o2c.getKey(), o2c.getValue());
		}


		// Initialize assignments (missing means default)
		_state      = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_interm     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_nextState  = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_observ     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_actions    = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_nonfluents = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();

		// Initialize variable lists
		_alStateNames.clear();
		_alNonFluentNames.clear();
		_alActionNames.clear();
		_alObservNames.clear();
		_alIntermNames.clear();
		for (Map.Entry<PVAR_NAME,PVARIABLE_DEF> e : _hmPVariables.entrySet()) {
			PVAR_NAME pname   = e.getKey();
			PVARIABLE_DEF def = e.getValue();
			if (def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alStateNames.add(pname);
				_state.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
				_nextState.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alNonFluentNames.add(pname);
				_nonfluents.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_ACTION_DEF) {
				_alActionNames.add(pname);
				_actions.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_OBS_DEF) {
				_alObservNames.add(pname);
				_observ.put(pname, new HashMap<ArrayList<LCONST>,Object>());
			} else if (def instanceof PVARIABLE_INTERM_DEF) {
				_alIntermNames.add(pname);
				_tmIntermNames.put(new Pair(((PVARIABLE_INTERM_DEF)def)._nLevel, pname), pname);
				_interm.put(pname, new HashMap<ArrayList<LCONST>,Object>());
			}
		}
		_hmTypeMap.put("states", _alStateNames);
		_hmTypeMap.put("nonfluent", _alNonFluentNames);
		_hmTypeMap.put("action", _alActionNames);
		_hmTypeMap.put("observ", _alObservNames);
		_hmTypeMap.put("interm", _alIntermNames);

		// Set initial state and pvariables
		if(!InitAggState(s)){
			System.out.println("Init fail");
		}
	}

	public void SetActNoCompute(ArrayList<PVAR_INST_DEF> actions)
		throws EvalException{

		// Clear then set the actions
		for (PVAR_NAME p : _actions.keySet())
			_actions.get(p).clear();
		setPVariables(_actions, actions);
	}
	
	public void init(TEState s) throws EvalException {
		
		_hmPVariables = s._hmPVariables;
		_hmTypes = s._hmTypes;
		_hmCPFs = s._hmCPFs;
		_alActionPreconditions = s._alActionPreconditions;
		_alStateInvariants = s._alStateInvariants;
		_reward = s._reward;
		_nMaxNondefActions = s._nMaxNondefActions;
		
		// Map object class name to list
		_hmObject2Consts = new HashMap<TYPE_NAME,ArrayList<LCONST>>();
		for (Map.Entry<TYPE_NAME,ArrayList<LCONST>> o2c : s._hmObject2Consts.entrySet()) {
			_hmObject2Consts.put(o2c.getKey(), o2c.getValue());
		}


		// Initialize assignments (missing means default)
		_state      = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_interm     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_nextState  = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_observ     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_actions    = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_nonfluents = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();

		// Initialize variable lists
		_alStateNames.clear();
		_alNonFluentNames.clear();
		_alActionNames.clear();
		_alObservNames.clear();
		_alIntermNames.clear();
		for (Map.Entry<PVAR_NAME,PVARIABLE_DEF> e : _hmPVariables.entrySet()) {
			PVAR_NAME pname   = e.getKey();
			PVARIABLE_DEF def = e.getValue();
			if (def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alStateNames.add(pname);
				_state.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
				_nextState.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alNonFluentNames.add(pname);
				_nonfluents.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_ACTION_DEF) {
				_alActionNames.add(pname);
				_actions.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_OBS_DEF) {
				_alObservNames.add(pname);
				_observ.put(pname, new HashMap<ArrayList<LCONST>,Object>());
			} else if (def instanceof PVARIABLE_INTERM_DEF) {
				_alIntermNames.add(pname);
				_tmIntermNames.put(new Pair(((PVARIABLE_INTERM_DEF)def)._nLevel, pname), pname);
				_interm.put(pname, new HashMap<ArrayList<LCONST>,Object>());
			}
		}
		_hmTypeMap.put("states", _alStateNames);
		_hmTypeMap.put("nonfluent", _alNonFluentNames);
		_hmTypeMap.put("action", _alActionNames);
		_hmTypeMap.put("observ", _alObservNames);
		_hmTypeMap.put("interm", _alIntermNames);

		// Set initial state and pvariables
		if(!InitAggState(s)){
			System.out.println("Init fail");
		}
		
	}

	public void init(HashMap<TYPE_NAME,OBJECTS_DEF> domain_objects,
					 HashMap<TYPE_NAME,OBJECTS_DEF> nonfluent_objects,
					 HashMap<TYPE_NAME,OBJECTS_DEF> instance_objects,
					 HashMap<TYPE_NAME,TYPE_DEF> typedefs,
					 HashMap<PVAR_NAME,PVARIABLE_DEF> pvariables,
					 HashMap<PVAR_NAME,CPF_DEF> cpfs,
					 ArrayList<PVAR_INST_DEF> init_state,
					 ArrayList<PVAR_INST_DEF> nf_nonfluents,
					 ArrayList<PVAR_INST_DEF> i_nonfluents,
					 ArrayList<BOOL_EXPR> state_action_constraints, // deprecated but still usable
					 ArrayList<BOOL_EXPR> action_preconditions,
					 ArrayList<BOOL_EXPR> state_invariants,
					 EXPR reward, 
					 int max_nondef_actions) {
		
		_hmPVariables = pvariables;
		_hmTypes = typedefs;
		_hmCPFs = cpfs;
		
		//_alConstraints = state_action_constraints; 
		_alActionPreconditions = new ArrayList<BOOL_EXPR>(); 
		_alActionPreconditions.addAll(action_preconditions);
		
		// Deprecated but we still have to support -- put them in action preconditions
		// since action preconditions are checked at the same point where state-action
		// constraints were previously checked
		_alActionPreconditions.addAll(state_action_constraints); 

		// State invariants are new in RDDL2 -- cannot mention actions or next-state variables
		// (checked in every state upon initially reaching that state)
		_alStateInvariants = new ArrayList<BOOL_EXPR>(); 
		_alStateInvariants.addAll(state_invariants);
		
		_reward = reward;
		_nMaxNondefActions = max_nondef_actions;
		
		// =============================
		
		// Map object/enum class name to list (NOTE: all enum and object value lists initialized here)
		// (Now that we allow superclasses we first have to preprocess all object definitions and ensure
		//  that we instantiate parents before children and then recursively instantiate children)
		
		_hmObject2Consts = new HashMap<TYPE_NAME,ArrayList<LCONST>>();
		if (domain_objects != null)
			for (OBJECTS_DEF obj_def : domain_objects.values())
				addConstants(obj_def._sObjectClass, obj_def._alObjects);
		if (nonfluent_objects != null)
			for (OBJECTS_DEF obj_def : nonfluent_objects.values())
				addConstants(obj_def._sObjectClass, obj_def._alObjects);
		if (instance_objects != null)
			for (OBJECTS_DEF obj_def : instance_objects.values())
				addConstants(obj_def._sObjectClass, obj_def._alObjects);
		for (Map.Entry<TYPE_NAME,TYPE_DEF> e : typedefs.entrySet()) {
			if (e.getValue() instanceof ENUM_TYPE_DEF) {
				ENUM_TYPE_DEF etd = (ENUM_TYPE_DEF)e.getValue();
				ArrayList<LCONST> values = new ArrayList<LCONST>();
				for (LCONST v : etd._alPossibleValues)
					values.add(v);
				addConstants(etd._sName, values);
			}
		}

		HashMap<TYPE_NAME,ArrayList<LCONST>> inheritedObjects = new HashMap<TYPE_NAME,ArrayList<LCONST>>();
		
		// Now add in constants to superclasses as well
		for (TYPE_NAME tname : _hmObject2Consts.keySet()) {
				
			// Add superclass constants for each tname
			TYPE_NAME cur_tname = tname;
			while (true) {
				// Terminate loop if enum or no superclass
				ArrayList<LCONST> child_constants = _hmObject2Consts.get(cur_tname);
				TYPE_DEF def = typedefs.get(cur_tname);
				if (!(def instanceof OBJECT_TYPE_DEF) || ((OBJECT_TYPE_DEF)def)._typeSuperclass == null)
					break;

				// We have a superclass, so add it's constants
				cur_tname = ((OBJECT_TYPE_DEF)def)._typeSuperclass; // Update for future iterations
				//ArrayList<LCONST> constants = _hmObject2Consts.get(cur_tname);
				//addConstants(cur_tname, child_constants);
				inheritedObjects.put(cur_tname, child_constants);
			}
		}

		for (HashMap.Entry<TYPE_NAME,ArrayList<LCONST>> entry : inheritedObjects.entrySet()) {
			addConstants(entry.getKey(), entry.getValue());
		}

		// =============================
		
		// TODO: Expand enum and object types according to the constants
		for (Map.Entry<TYPE_NAME,TYPE_DEF> e : typedefs.entrySet()) {
			if (e.getValue() instanceof STRUCT_TYPE_DEF && ((STRUCT_TYPE_DEF)e.getValue())._typeGeneric != null) {
				STRUCT_TYPE_DEF ldef = (STRUCT_TYPE_DEF)e.getValue();
				ArrayList<LCONST> constants = _hmObject2Consts.get(ldef._sLabelEnumOrObjectType);
				if (constants == null) {
					System.err.println("Could not instantiate object tuple\n" + ldef + 
							"\nwith constants from '" + ldef._sLabelEnumOrObjectType+ "'");
					System.exit(1);
				}
				ldef.initIndefiniteTypes(constants);
			}
		}

		// Initialize assignments (missing means default)
		_state      = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_interm     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_nextState  = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_observ     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_actions    = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		_nonfluents = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>>();
		
		// Initialize variable lists and vector defaults (if needed)
		_alStateNames.clear();
		_alNonFluentNames.clear();
		_alActionNames.clear();
		_alObservNames.clear();
		_alIntermNames.clear();
		boolean undefined_levels = false;
		for (Map.Entry<PVAR_NAME,PVARIABLE_DEF> e : _hmPVariables.entrySet()) {
			PVAR_NAME pname   = e.getKey();
			PVARIABLE_DEF def = e.getValue();
						
			// Expand the default value definition if it is a vector containing <? : type>
			if (def instanceof PVARIABLE_WITH_DEFAULT_DEF) {
				PVARIABLE_WITH_DEFAULT_DEF ddef = (PVARIABLE_WITH_DEFAULT_DEF)def;
						
				// If the default value is a vector type, we should instantiate it
				// (in case it contains a <? : val> expansion type)
				if (ddef._oDefValue instanceof STRUCT_VAL) {
					String msg_def_value = def + " with " + ddef._oDefValue.toString(); // Save in case of error since we overwrite
					try {
						((STRUCT_VAL)ddef._oDefValue).instantiate(ddef._typeRange, typedefs, _hmObject2Consts);
					} catch (Exception e2) {
						System.err.println("ERROR: Could not instantiate object tuple: " + msg_def_value +
								"\n... check definition and that all subtypes and object/enum lists are defined.\n" + e2);
						System.exit(1);
					}
				}
			}
			
			// Book-keeping for all PVARIABLEs
			if (def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alStateNames.add(pname);
				_state.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
				_nextState.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alNonFluentNames.add(pname);
				_nonfluents.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_ACTION_DEF) {
				_alActionNames.add(pname);
				_actions.put(pname, new HashMap<ArrayList<LCONST>, TreeExp>());
			} else if (def instanceof PVARIABLE_OBS_DEF) {
				_alObservNames.add(pname);
				_observ.put(pname, new HashMap<ArrayList<LCONST>,Object>());
			} else if (def instanceof PVARIABLE_INTERM_DEF) {
				int level = ((PVARIABLE_INTERM_DEF)def)._nLevel;
				if (level < 0)
					undefined_levels = true; 
				_alIntermNames.add(pname);
				_tmIntermNames.put(new Pair(level, pname), pname);
				_interm.put(pname, new HashMap<ArrayList<LCONST>,Object>());
			}
		}
		_hmTypeMap.put("states", _alStateNames);
		_hmTypeMap.put("nonfluent", _alNonFluentNames);
		_hmTypeMap.put("action", _alActionNames);
		_hmTypeMap.put("observ", _alObservNames);
		_hmTypeMap.put("interm", _alIntermNames);

		// Set initial state and pvariables
		setPVariables(_state, init_state);
		setPVariables(_nonfluents, nf_nonfluents);
		setPVariables(_nonfluents, i_nonfluents);
			
		// Derive fluent ordering
		try {
			_r2g = new TERDDL2Graph(this);
			deriveDAGOrdering();
			//System.out.println("Derived: " + _alDerivedGfluentOrdering);
			//System.out.println("Interm:  " + _alIntermGfluentOrdering);
		} catch (Exception e) {
			System.out.println("Could not derive legal fluent ordering:\n" + e);
			e.printStackTrace();
			System.exit(1);
		}
		
		// Compute derived fluents from state
		try {
			computeDerivedFluents();
		} catch (EvalException e) {
			System.out.println("Could not evaluate/initialize derived fluents in initial state:\n" + e);
			System.out.println("**Ensure that derived fluents only depend on other derived fluents and state fluents (not intermediate or observation fluents)");
			System.exit(1);
		}
	}
	
	private void deriveDAGOrdering() throws Exception {

		// First we need to detect cycles and exit if we found any		
		if (_r2g._graph.hasCycle()) {
		
			// General loops
			StringBuilder msg = new StringBuilder();
			msg.append("\nERROR: the DBN dependency graph contains one or more cycles as follows:");
			HashSet<HashSet<Object>> sccs = _r2g._graph.getStronglyConnectedComponents();
			for (HashSet<Object> connected_component : sccs)
				if (connected_component.size() > 1)
					System.err.println("- Cycle: " + connected_component);
			
			// Self-cycles 
			HashSet<Object> self_cycles = _r2g._graph.getSelfCycles();
			for (Object v : self_cycles)
				msg.append("- Self-cycle: [" + v + "]");
			
			throw new Exception(msg.toString());
		}
		
		// No cycles, extract an ordering
		List ordering = _r2g._graph.topologicalSort(false);
		for (Object fluent_name : ordering) {		
			Pair gfluent = _r2g._hmName2IntermGfluent.get((String)fluent_name);

			// We only want interms and derived predicates and only these are in the HashMap
			if (gfluent != null) { 

				PVARIABLE_INTERM_DEF def = (PVARIABLE_INTERM_DEF)_hmPVariables.get((PVAR_NAME)gfluent._o1);
				
				// Separate lists, eval derived then interm, add parents before children since we have to evaluate top-down
				if (def._bDerived)
					_alDerivedGfluentOrdering.add(gfluent); 
				else						
					_alIntermGfluentOrdering.add(gfluent); 
			}
		}
	}

	public void addConstants(TYPE_NAME object_class, ArrayList<LCONST> constants) {
		
		// First check that object_class is defined 
		if (!(_hmTypes.get(object_class) instanceof RDDL.OBJECT_TYPE_DEF) &&
			!(_hmTypes.get(object_class) instanceof RDDL.ENUM_TYPE_DEF)) {
			System.err.println("FATAL ERROR: '" + 
					object_class + "' is not a defined object/enum type; " + 
					"cannot initialize with " + constants + ".");
			System.exit(1);
		}
		
		// Merge constants without duplication
		ArrayList<LCONST> new_constants = new ArrayList<LCONST>(constants);
		ArrayList<LCONST> cur_constants = _hmObject2Consts.get(object_class);
		if (cur_constants != null) 
			for (LCONST c : cur_constants)
				if (!new_constants.contains(c))
					new_constants.add(c);
		_hmObject2Consts.put(object_class, new_constants);
	}
	
	public TreeExp checkStateActionConstraints(ArrayList<PVAR_INST_DEF> actions)  
		throws EvalException {
		
		// Clear then set the actions
		for (PVAR_NAME p : _actions.keySet())
			_actions.get(p).clear();
		int non_def = setPVariables(_actions, actions);

		// Check max-nondef actions
		if (non_def > _nMaxNondefActions)
			throw new EvalException("Number of non-default actions (" + non_def + 
					") exceeds limit (" + _nMaxNondefActions + ")");
		
		// Check state-action constraints
		HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
		TreeExp availability = TreeExp.BuildNewTreeExp(1.0, null);
		for (BOOL_EXPR constraint : _alActionPreconditions) {
			// satisfied must be true if get here
			availability = availability.TIMES(toTExp(constraint.sample(subs, this, null), null));
			if( availability.term != null && availability.term.var == -1 && availability.term.coefficient == 0.0 ){
				break;
			}
		}
		return availability;
	}

	public void checkStateInvariants()  
			throws EvalException {
			
		// Check state invariants 
		// (should not mention actions or next state variables -- 
		//  nothing to substitute since current state known)
		HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
		for (BOOL_EXPR constraint : _alStateInvariants) {
			// satisfied must be true if get here
			try {
				if (! (Boolean)constraint.sample(subs, this, null) )
					throw new EvalException("\nViolated state invariant constraint: " + constraint + 
							"\nNOTE: state invariants should never be violated by a correctly defined transition model starting from a legal initial state.\n" + 
							"**in state**\n" + this);
			} catch (NullPointerException e) {
				System.out.println("\n***SIMULATOR ERROR EVALUATING: " + constraint);
				throw e;
			} catch (ClassCastException e) {
				System.out.println("\n***SIMULATOR ERROR EVALUATING: " + constraint);
				throw e;
			}
		}
	}

	public boolean checkTerminationCondition(BOOL_EXPR cond) throws EvalException {
		try {
			HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
			return (Boolean)cond.sample(subs, this, null);
		} catch (EvalException e) {
			System.out.println("\n***SIMULATOR ERROR EVALUATING TERMINATION CONDITION: " + cond);
			throw e;
		}
	}
	
	public void computeNextState(RandomDataGenerator r)
			throws EvalException{
			// System.out.println("Starting state: " + _state + "\n");
			// System.out.println("Starting nonfluents: " + _nonfluents + "\n");

			// First compute intermediate variables, level-by-level
			HashMap<LVAR, LCONST> subs = new HashMap<LVAR, LCONST>();
			if (DISPLAY_UPDATES)
				System.out.println("Updating intermediate variables");
			for (Map.Entry<Pair, PVAR_NAME> e : _tmIntermNames.entrySet()) {
				int level = (Integer) e.getKey()._o1;
				PVAR_NAME p = e.getValue();

				// Generate updates for each ground fluent
				// System.out.println("Updating interm var " + p + " @ level " +
				// level + ":");
				ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);

				for (ArrayList<LCONST> gfluent : gfluents) {
					if (DISPLAY_UPDATES)
						System.out.print("- " + p + gfluent + " @ " + level
								+ " := ");
					CPF_DEF cpf = _hmCPFs.get(p);

					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR) cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST) gfluent.get(i);
						subs.put(v, c);
					}
					

					Object value = cpf._exprEquals.sample(subs, this, r);


					//String v = value.toString();
					if (DISPLAY_UPDATES)
						System.out.println(value);

					// Update value
					HashMap<ArrayList<LCONST>, Object> pred_assign = _interm.get(p);
					pred_assign.put(gfluent, value);
				}
			}

			// Do same for next-state (keeping in mind primed variables)
			if (DISPLAY_UPDATES)
				System.out.println("Updating next state");
			for (PVAR_NAME p : _alStateNames) {

				// Get default value
				Object def_value = null;
				PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
				if (!(pvar_def instanceof PVARIABLE_STATE_DEF)
						|| ((PVARIABLE_STATE_DEF) pvar_def)._bNonFluent)
					throw new EvalException(
							"Expected state variable, got nonfluent: " + p);
				def_value = ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;

				// Generate updates for each ground fluent
				PVAR_NAME primed = new PVAR_NAME(p._sPVarName + "'");
				// System.out.println("Updating next state var " + primed + " (" + p
				// + ")");
				ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);

				for (ArrayList<LCONST> gfluent : gfluents) {
					if (DISPLAY_UPDATES)
						System.out.print("- " + primed + gfluent + " := ");
					CPF_DEF cpf = _hmCPFs.get(primed);

					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR) cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST) gfluent.get(i);
						subs.put(v, c);
					}

					//TreeExp value = (TreeExp)cpf._exprEquals.sample(subs, this, r);
					TreeExp value = toTExp(cpf._exprEquals.sample(subs, this, r), null);
					//String v = value.toString();
					//System.out.println(primed._sPVarName + subs + " = " + v);
					if (DISPLAY_UPDATES)
						System.out.println(value);

					// Update value if not default
					if (!value.equals(def_value)) {
						HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _nextState.get(p);
						pred_assign.put(gfluent, toTExp(value, null));
					}
				}
			}

			// Make sure observations are cleared prior to computing new ones
			for (PVAR_NAME p : _observ.keySet())
				_observ.get(p).clear();

			// Do same for observations... note that this occurs after the next
			// state
			// update because observations in a POMDP may be modeled on the current
			// and next state, i.e., P(o|s,a,s').
			if (DISPLAY_UPDATES)
				System.out.println("Updating observations");
			for (PVAR_NAME p : _alObservNames) {
				throw new EvalException(
						"POMDP not supprted yet: Astate-Computenextstate()");
				// Generate updates for each ground fluent
				// System.out.println("Updating observation var " + p);
				/*
				 * ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
				 * 
				 * for (ArrayList<LCONST> gfluent : gfluents) { if (DISPLAY_UPDATES)
				 * System.out.print("- " + p + gfluent + " := "); CPF_DEF cpf =
				 * _hmCPFs.get(p);
				 * 
				 * subs.clear(); for (int i = 0; i <
				 * cpf._exprVarName._alTerms.size(); i++) { LVAR v =
				 * (LVAR)cpf._exprVarName._alTerms.get(i); LCONST c =
				 * (LCONST)gfluent.get(i); subs.put(v,c); }
				 * 
				 * Object value = cpf._exprEquals.sample(subs, this, r); if
				 * (DISPLAY_UPDATES) System.out.println(value);
				 * 
				 * // Update value HashMap<ArrayList<LCONST>,Object> pred_assign =
				 * _observ.get(p); pred_assign.put(gfluent, value); }
				 */
			}
		}
	
	public void computeNextState(ArrayList<PVAR_INST_DEF> actions, RandomDataGenerator _rand) 
		throws EvalException {

		// Clear then set the actions
		for (PVAR_NAME p : _actions.keySet())
			_actions.get(p).clear();
		setPVariables(_actions, actions);
		
		//System.out.println("Starting state: " + _state + "\n");
		//System.out.println("Starting nonfluents: " + _nonfluents + "\n");
		
		// First compute intermediate variables (derived should have already been computed)
		HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
		if (DISPLAY_UPDATES) System.out.println("Updating intermediate variables");
		for (Pair ifluent : _alIntermGfluentOrdering) {
			
			PVAR_NAME p = (PVAR_NAME)ifluent._o1;
			ArrayList<LCONST> gfluent = (ArrayList<LCONST>)ifluent._o2;
			
			if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent);
			CPF_DEF cpf = _hmCPFs.get(p);
			if (cpf == null) 
				throw new EvalException("Could not find cpf for: " + p + gfluent);
			
			subs.clear();
			for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
				LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
				LCONST c = (LCONST)gfluent.get(i);
				subs.put(v,c);
			}
			
			Object value = cpf._exprEquals.sample(subs, this, _rand);
			if (DISPLAY_UPDATES) System.out.println(value);
			
			// Update value
			HashMap<ArrayList<LCONST>,Object> pred_assign = _interm.get(p);
			pred_assign.put(gfluent, value);
		}
		
		// Do same for next-state (keeping in mind primed variables)
		if (DISPLAY_UPDATES) System.out.println("Updating next state");
		for (PVAR_NAME p : _alStateNames) {
						
			// Get default value
			Object def_value = null;
			PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
			if (!(pvar_def instanceof PVARIABLE_STATE_DEF) ||
				((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
				throw new EvalException("Expected state variable, got nonfluent: " + p);
			def_value = ((PVARIABLE_STATE_DEF)pvar_def)._oDefValue;
			
			// Generate updates for each ground fluent
			PVAR_NAME primed = new PVAR_NAME(p._sPVarName + "'");
			//System.out.println("Updating next state var " + primed + " (" + p + ")");
			ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
			
			for (ArrayList<LCONST> gfluent : gfluents) {
				if (DISPLAY_UPDATES) System.out.print("- " + primed + gfluent + " := ");
				CPF_DEF cpf = _hmCPFs.get(primed);
				if (cpf == null) 
					throw new EvalException("Could not find cpf for: " + primed + 
							"... did you forget to prime (') the variable in the cpf definition?");
				
				subs.clear();
				for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
					LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
					LCONST c = (LCONST)gfluent.get(i);
					subs.put(v,c);
				}
				
				Object value = cpf._exprEquals.sample(subs, this, _rand);
				if (DISPLAY_UPDATES) System.out.println(value);
				
				// Update value if not default
				if (!value.equals(def_value)) {
					HashMap<ArrayList<LCONST>, TreeExp> pred_assign = _nextState.get(p);
					pred_assign.put(gfluent, toTExp(value, null));
				}
			}
		}
		
		// Make sure observations are cleared prior to computing new ones
		for (PVAR_NAME p : _observ.keySet())
			_observ.get(p).clear();

		// Do same for observations... note that this occurs after the next state
		// update because observations in a POMDP may be modeled on the current
		// and next state, i.e., P(o'|s,a,s').
		if (DISPLAY_UPDATES) System.out.println("Updating observations");
		for (PVAR_NAME p : _alObservNames) {
			
			// Generate updates for each ground fluent
			//System.out.println("Updating observation var " + p);
			ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
			
			for (ArrayList<LCONST> gfluent : gfluents) {
				if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent + " := ");
				CPF_DEF cpf = _hmCPFs.get(p);
				if (cpf == null) 
					throw new EvalException("Could not find cpf for: " + p);
	
				subs.clear();
				for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
					LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
					LCONST c = (LCONST)gfluent.get(i);
					subs.put(v,c);
				}
				
				Object value = cpf._exprEquals.sample(subs, this, _rand);
				if (DISPLAY_UPDATES) System.out.println(value);
				
				// Update value
				HashMap<ArrayList<LCONST>,Object> pred_assign = _observ.get(p);
				pred_assign.put(gfluent, value);
			}
		}
	}
	
	public void computeDerivedFluents() throws EvalException {
		
		// Compute derived variables in order
		HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
		if (DISPLAY_UPDATES) System.out.println("Updating intermediate variables");
		for (Pair ifluent : _alDerivedGfluentOrdering) {
			
			PVAR_NAME p = (PVAR_NAME)ifluent._o1;
			ArrayList<LCONST> gfluent = (ArrayList<LCONST>)ifluent._o2;
			
			if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent);
			CPF_DEF cpf = _hmCPFs.get(p);
			if (cpf == null) 
				throw new EvalException("Could not find cpf for: " + p + gfluent);
			
			subs.clear();
			for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
				LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
				LCONST c = (LCONST)gfluent.get(i);
				subs.put(v,c);
			}
			
			if (!cpf._exprEquals._bDet)
				throw new EvalException("Derived fluent " + p + gfluent + " cannot have stochastic definition: " + cpf._exprEquals);

			// No randomness for derived fluents (can pass null)
			Object value = cpf._exprEquals.sample(subs, this, null);
			if (DISPLAY_UPDATES) System.out.println(value);
			
			// Update value
			HashMap<ArrayList<LCONST>,Object> pred_assign = _interm.get(p);
			pred_assign.put(gfluent, value);
		}		
	}
	
	public void advanceNextState() throws EvalException {
		// For backward compatibility with code that has previously called this
		// method with 0 parameters, we'll assume observations are cleared by default
		advanceNextState(true /* clear observations */);
	}
	
	public void advanceNextState(boolean clear_observations) throws EvalException {
		HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>> temp = _state;
		_state = _nextState;
		_nextState = temp;
		
		// Clear the non-state, non-constant, non-action variables
		for (PVAR_NAME p : _nextState.keySet())
			_nextState.get(p).clear();
		//for (PVAR_NAME p : _interm.keySet())
			//_interm.get(p).clear();
		if (clear_observations)  
			for (PVAR_NAME p : _observ.keySet())
				_observ.get(p).clear();
		
		// Compute derived fluents from new state
		computeDerivedFluents();
	}
	
	public void clearPVariables(HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>> assign) {
		for (HashMap<ArrayList<LCONST>,Object> pred_assign : assign.values())
			pred_assign.clear();
	}
	
	public int setPVariables(HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>, TreeExp>> assign, 
							  ArrayList<PVAR_INST_DEF> src) {

		int non_def = 0;
		boolean fatal_error = false;
		for (PVAR_INST_DEF def : src) {
			
			// Get the assignments for this PVAR
			HashMap<ArrayList<LCONST>, TreeExp> pred_assign = assign.get(def._sPredName);
			if (pred_assign == null) {
				System.out.println("FATAL ERROR: '" + def._sPredName + "' not defined");
				fatal_error = true;
			}
			
			// Get default value if it exists
			Object def_value = null;
			PVARIABLE_DEF pvar_def = _hmPVariables.get(def._sPredName);
			if (pvar_def instanceof PVARIABLE_STATE_DEF) // state & non_fluents
				def_value = ((PVARIABLE_STATE_DEF)pvar_def)._oDefValue;
			else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) // actions
				def_value = ((PVARIABLE_ACTION_DEF)pvar_def)._oDefValue;
			
			// Set value if non-default
			if (def_value != null && !def_value.equals(def._oValue)) {
				try {
					pred_assign.put(def._alTerms, toTExp(def._oValue, null));
				} catch (EvalException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				++non_def;
			} else if ( pvar_def instanceof PVARIABLE_OBS_DEF ) {
				try {
					pred_assign.put(def._alTerms, toTExp(def._oValue, null));
				} catch (EvalException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		
		if (fatal_error) {
			System.out.println("ABORTING DUE TO FATAL ERRORS");
			System.exit(1);
		}
		
		return non_def;
	}

	/////////////////////////////////////////////////////////////////////////////
	//             Methods for Querying and Setting Fluent Values
	/////////////////////////////////////////////////////////////////////////////
	
	public Object getPVariableDefault(PVAR_NAME p) {
		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
		if (pvar_def instanceof PVARIABLE_STATE_DEF) // state & non_fluents
			return ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;
		else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) // actions
			return ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;
		return null;
	}
	
	public int getPVariableType(PVAR_NAME p) {
		
		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);

		if (pvar_def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			return NONFLUENT;
		else if (pvar_def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			return STATE;
		else if (pvar_def instanceof PVARIABLE_ACTION_DEF)
			return ACTION;
		else if (pvar_def instanceof PVARIABLE_INTERM_DEF)
			return INTERM;
		else if (pvar_def instanceof PVARIABLE_OBS_DEF)
			return OBSERV;
		
		return UNDEFINED;
	}
	
	public Object getDefaultValue(PVAR_NAME p) {
		
		Object def_value = null;
		PVARIABLE_DEF pvar_def = _hmPVariables.get(new PVAR_NAME(p._sPVarName));
		if (pvar_def instanceof PVARIABLE_STATE_DEF) // state & non_fluents
			def_value = ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;
		else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) // actions
			def_value = ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;
		return def_value;
	}
	
	public Object getPVariableAssign(PVAR_NAME p, ArrayList<LCONST> terms) throws EvalException {

		// Get default value if it exists
		Object def_value = null;
		boolean primed = p._bPrimed;
		p = p._pvarUnprimed; // We'll look up the unprimed version, but check for priming later
		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
		
		if (pvar_def == null)
			throw new EvalException("ERROR: undefined pvariable: " + p);
		else if (pvar_def._alParamTypes.size() != terms.size()) 
			throw new EvalException("ERROR: expected " + pvar_def._alParamTypes.size() + 
					" parameters for " + p + ", but got " + terms.size() + ": " + terms);
		
		// Initialize with defaults in case not assigned
		if (pvar_def instanceof PVARIABLE_STATE_DEF) { // state & non_fluents
			def_value = ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;
			if (def_value == null)
				throw new EvalException("ERROR: Default value should not be null for state fluent " + pvar_def);
		} else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) { // actions
			def_value = ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;
			if (def_value == null)
				throw new EvalException("ERROR: Default value should not be null for action fluent " + pvar_def);
		}
		//System.out.println("Default value: " + def_value);

		// Get correct variable assignments
		HashMap<ArrayList<LCONST>, Object> var_src = null;
		HashMap<ArrayList<LCONST>, TreeExp> var_src_stat = null;
		if (pvar_def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = _nonfluents.get(p);
		else if (pvar_def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = /*CHECK PRIMED*/ primed ? _nextState.get(p) : _state.get(p); // Note: (next) state index by non-primed pvar
		else if (pvar_def instanceof PVARIABLE_ACTION_DEF)
			var_src_stat = _actions.get(p);
		else if (pvar_def instanceof PVARIABLE_INTERM_DEF)
			var_src = _interm.get(p);
		else if (pvar_def instanceof PVARIABLE_OBS_DEF)
			var_src = _observ.get(p);
			
		if (var_src == null && var_src_stat == null)
			throw new EvalException("ERROR: no variable source for " + p);
		
		// Lookup value, return default (if available) if value not found
		Object ret = null;
		if(var_src != null){
			ret = var_src.get(terms);
		}
		else{
			ret = var_src_stat.get(terms);
		}
		if (ret == null)
			ret = def_value;

		return ret;
	}
	
	//decide if all item in possibleSub is a sub class of possibleSuper
	static public boolean IfSuperClassList(ArrayList<TYPE_NAME> possibleSub, ArrayList<TYPE_NAME> possibleSuper) {
		//same pvar_name should have the same number of arguments
		//just in case
		if(possibleSub.size() != possibleSuper.size()) {
			return false;
		}
		for(int i = 0; i < possibleSub.size(); i ++) {
			TYPE_NAME tn = possibleSub.get(i);
			if(!tn._STypeName.equals(possibleSuper.get(i)._STypeName)) {
				//ArrayList<TYPE_NAME> aaa = Policy.superClass.get(tn);
				if((!Policy.superClass.containsKey(tn) || !Policy.superClass.get(tn).contains(possibleSuper.get(i)))) {
					return false;
				}
			}
		}
		return true;
	}
	
	//make another copy the current TEState
	//this should be fast and quick 
	//only used to evaluate state variables or expressions that only contains state variables inside
	//
	public TEState QuickCopy() throws EvalException{
		TEState res = new TEState();
		res._state = new HashMap<>();
		res._nonfluents = new HashMap<>();
		for(PVAR_NAME theP: _alStateNames) {
			if(_state.containsKey(theP)) {
				if(!res._state.containsKey(theP)) {
					res._state.put(theP, new HashMap<>());
				}
				for(ArrayList<LCONST> theConst: generateAtoms(theP)) {
					if(_state.get(theP).containsKey(theConst)) {
						res._state.get(theP).put(theConst, _state.get(theP).get(theConst));
					}
				}
			}
		}
		for(PVAR_NAME theP: _alNonFluentNames) {
			if(_nonfluents.containsKey(theP)) {
				if(!res._nonfluents.containsKey(theP)) {
					res._nonfluents.put(theP, new HashMap<>());
				}
				for(ArrayList<LCONST> theConst: generateAtoms(theP)) {
					if(_nonfluents.get(theP).containsKey(theConst)) {
						res._nonfluents.get(theP).put(theConst, _nonfluents.get(theP).get(theConst));
					}
				}
			}
		}
		
		res._hmObject2Consts = new HashMap<>();
		Iterator it =  _hmObject2Consts.entrySet().iterator();
		//first figure out which are the variables used in for this PVAR_NAME
	    while (it.hasNext()) {
	        Map.Entry pair = (Map.Entry)it.next();
	        res._hmObject2Consts.put((TYPE_NAME)pair.getKey(), (ArrayList<RDDL.LCONST>)pair.getValue());
	    }
	    
	    res._hmPVariables = new HashMap<>();
		it = _hmPVariables.entrySet().iterator();
		//first figure out which are the variables used in for this PVAR_NAME
	    while (it.hasNext()) {
	        Map.Entry pair = (Map.Entry)it.next();
	        res._hmPVariables.put((PVAR_NAME)pair.getKey(), (PVARIABLE_DEF)pair.getValue());
	    }
	    
	    return res;
	}
	
	//only needed when not building the graph but return emergency action
	public TEState QuickCopy(State s) throws EvalException{
		TEState res = new TEState();
		res._state = new HashMap<>();
		res._nonfluents = new HashMap<>();
		for(PVAR_NAME theP: s._alStateNames) {
			if(s._state.containsKey(theP)) {
				if(!res._state.containsKey(theP)) {
					res._state.put(theP, new HashMap<>());
				}
				for(ArrayList<LCONST> theConst: s.generateAtoms(theP)) {
					if(s._state.get(theP).containsKey(theConst)) {
						double theD = 0.0;
						Object theVal = s._state.get(theP).get(theConst);
						if(theVal instanceof Double) {
							theD = (Double)theVal;
						}
						else {
							if(theVal instanceof Boolean && (Boolean)theVal) {
								theD = 1.0;
							}
						}
						res._state.get(theP).put(theConst, TreeExp.BuildNewTreeExp(theD, null));
					}
				}
			}
		}
		for(PVAR_NAME theP: s._alNonFluentNames) {
			if(s._nonfluents.containsKey(theP)) {
				if(!res._nonfluents.containsKey(theP)) {
					res._nonfluents.put(theP, new HashMap<>());
				}
				for(ArrayList<LCONST> theConst: s.generateAtoms(theP)) {
					if(s._nonfluents.get(theP).containsKey(theConst)) {
						double theD = 0.0;
						Object theVal = s._nonfluents.get(theP).get(theConst);
						if(theVal instanceof Double) {
							theD = (Double)theVal;
						}
						else {
							if(theVal instanceof Boolean && (Boolean)theVal) {
								theD = 1.0;
							}
						}
						res._nonfluents.get(theP).put(theConst, TreeExp.BuildNewTreeExp(theD, null));
					}
				}
			}
		}
		
		res._hmObject2Consts = new HashMap<>();
		Iterator it = s._hmObject2Consts.entrySet().iterator();
		//first figure out which are the variables used in for this PVAR_NAME
	    while (it.hasNext()) {
	        Map.Entry pair = (Map.Entry)it.next();
	        res._hmObject2Consts.put((TYPE_NAME)pair.getKey(), (ArrayList<RDDL.LCONST>)pair.getValue());
	    }
	    
	    res._hmPVariables = new HashMap<>();
		it = s._hmPVariables.entrySet().iterator();
		//first figure out which are the variables used in for this PVAR_NAME
	    while (it.hasNext()) {
	        Map.Entry pair = (Map.Entry)it.next();
	        res._hmPVariables.put((PVAR_NAME)pair.getKey(), (PVARIABLE_DEF)pair.getValue());
	    }
	    
	    return res;
	}
	
	@SuppressWarnings("unchecked")
	public Object getPVariableAssign(PVAR_NAME p, ArrayList<LTERM> alVar, ArrayList<LCONST> terms, HashMap<LVAR, LCONST> subs) throws EvalException {
		
		// get the lvar map
		HashMap<LCONST, LVAR> vars = new HashMap<>();
		for (Map.Entry<LVAR, LCONST> e : subs.entrySet()) {
			vars.put(e.getValue(), e.getKey());
		}
	
		// Get default value if it exists
		Object def_value = null;
		boolean primed = p._bPrimed;
		p = p._pvarUnprimed; // We'll look up the unprimed version, but check for priming later

		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
		
		if (pvar_def == null)
			throw new EvalException("ERROR: undefined pvariable: " + p);
		else if (pvar_def._alParamTypes.size() != terms.size()) 
			throw new EvalException("ERROR: expected " + pvar_def._alParamTypes.size() + 
					" parameters for " + p + ", but got " + terms.size() + ": " + terms);

		// Initialize with defaults in case not assigned
		if (pvar_def instanceof PVARIABLE_STATE_DEF) { // state & non_fluents
			def_value = ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;
			if (def_value == null)
				throw new EvalException("ERROR: Default value should not be null for state fluent " + pvar_def);
		} else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) { // actions
			def_value = ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;
			if (def_value == null)
				throw new EvalException("ERROR: Default value should not be null for action fluent " + pvar_def);
		}
		
		//System.out.println("Default value: " + def_value);
		// Get correct variable assignments
		HashMap<ArrayList<LCONST>, Object> var_src = null;
		HashMap<ArrayList<LCONST>, TreeExp> var_src_stat = null;
		if (pvar_def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = _nonfluents.get(p);
		else if (pvar_def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = /*CHECK PRIMED*/ primed ? _nextState.get(p) : _state.get(p); // Note: (next) state index by non-primed pvar
		else if (pvar_def instanceof PVARIABLE_ACTION_DEF)
			var_src_stat = _actions.get(p);
		else if (pvar_def instanceof PVARIABLE_INTERM_DEF)
			var_src = _interm.get(p);
		else if (pvar_def instanceof PVARIABLE_OBS_DEF)
			var_src = _observ.get(p);
			
		if (var_src == null && var_src_stat == null)
			throw new EvalException("ERROR: no variable source for " + p);
		
		// Lookup value, return default (if available) if value not found
		Object ret = null;
		if(var_src != null){
			ret = var_src.get(terms);
		}
		else{
			ret = var_src_stat.get(terms);
		}
		if (ret == null)
			ret = def_value;

		TreeExp tret = toTExp(ret, null);
		//if(!Policy._ifDisAction){
		
		
		if (Policy._extraEffects.containsKey(p)) {
			// addVars.addAll(c)
			ArrayList<TYPE_NAME> typenames = LCONST2TYPE_NAME(terms, vars);
			HashMap<ArrayList<TYPE_NAME>, ArrayList<BOOL_EXPR>> possibleMaches = Policy._extraEffects.get(p);
			Iterator it = possibleMaches.entrySet().iterator();
			// first figure out which are the variables used in for this PVAR_NAME

			while (it.hasNext()) {
				Map.Entry pair = (Map.Entry) it.next();
				// first decide if the type of each parameter is a subclass of the type of
				// parameters in the preconditions
				ArrayList<TYPE_NAME> constraintsTypeName = (ArrayList<RDDL.TYPE_NAME>) pair.getKey();

				if (IfSuperClassList(typenames, constraintsTypeName)) {
					// times each additional effects to the action variables
					for (BOOL_EXPR theAddEff : (ArrayList<BOOL_EXPR>) pair.getValue()) {
						RandomDataGenerator newR = new RandomDataGenerator();
						// laod the substituion of lvars into newsub
						// pass new sub to the sampling of the constraints
						HashMap<LVAR, LCONST> newSubs = new HashMap<>();
						// deal with each parameter appeared in the precondition
						for (int i = 0; i < Policy._extraEffectsLVARS.get(p).get(constraintsTypeName).size(); i++) {
							// important:
							// we assume that there is no repetition of types in both the preconditions and
							// action variable subs
							LVAR theVar = (LVAR) Policy._extraEffectsLVARS.get(p).get(constraintsTypeName).get(i);
							newSubs.put(theVar, (LCONST) subs.get(alVar.get(i)));
						}
						if(newSubs.size() == 1 && theAddEff instanceof PVAR_EXPR && ((PVAR_EXPR)theAddEff)._alTerms.size() == 1) {
							Map.Entry<LVAR, LCONST> entry = newSubs.entrySet().iterator().next();
							LVAR key = entry.getKey();
							if(!key.toString().equals(((PVAR_EXPR)theAddEff)._alTerms.get(0).toString())) {
								LCONST value = entry.getValue();
								newSubs.put((LVAR)((PVAR_EXPR)theAddEff)._alTerms.get(0), value);
							}
						}
						TreeExp theT = TEState.toTExp(theAddEff.sample(newSubs, this, newR), null);
						
						newSubs.clear();
						newSubs = null;
						
						tret = tret.TIMES(theT);

						
						if (tret.term != null && tret.term.var == -1 && tret.term.coefficient == 0.0) {

							return TreeExp.BuildNewTreeExp(0.0, null);
						}
					}

				}
			}
		}
		vars.clear();
		vars = null;
		//System.out.println(p);
		return tret;
		
	}	
		
	public boolean setPVariableAssign(PVAR_NAME p, ArrayList<LCONST> terms, 
			Object value) {
		
		// Get default value if it exists
		Object def_value = null;
		boolean primed = p._bPrimed;
		p = new PVAR_NAME(p._sPVarName);
		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
		
		if (pvar_def == null) {
			System.out.println("ERROR: undefined pvariable: " + p);
			return false;
		} else if (pvar_def._alParamTypes.size() != terms.size()) {
			System.out.println("ERROR: expected " + pvar_def._alParamTypes.size() + 
					" parameters for " + p + ", but got " + terms.size() + ": " + terms);
			return false;
		}
		
		if (pvar_def instanceof PVARIABLE_STATE_DEF) // state & non_fluents
			def_value = ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;
		else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) // actions
			def_value = ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;

		// Get correct variable assignments
		HashMap<ArrayList<LCONST>,Object> var_src = null;
		HashMap<ArrayList<LCONST>, TreeExp> var_src_stat = null;
		if (pvar_def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = _nonfluents.get(p);
		else if (pvar_def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = primed ? _nextState.get(p) : _state.get(p); // Note: (next) state index by non-primed pvar
		else if (pvar_def instanceof PVARIABLE_ACTION_DEF)
			var_src_stat = _actions.get(p);
		else if (pvar_def instanceof PVARIABLE_INTERM_DEF)
			var_src = _interm.get(p);
		else if (pvar_def instanceof PVARIABLE_OBS_DEF)
			var_src = _observ.get(p);
		
		if (var_src == null) {
			System.out.println("ERROR: no variable source for " + p);
			return false;
		}

		// Set value (or remove if default)... n.b., def_value could be null if not s,a,s'
		if (value == null || value.equals(def_value)) {
			var_src.remove(terms);			
		} else {
			var_src.put(terms, value);
		}
		return true;
	}
	

	public void FindExprBitsPair(HashMap<LVAR,LCONST> subs, EXPR e){
		
	}
			
	//////////////////////////////////////////////////////////////////////
	public void UpdateRecord(EXPR e){
		if(e instanceof QUANT_EXPR){
			ArrayList<LTYPED_VAR> vars = ((QUANT_EXPR) e)._alVariables;
			for(LTYPED_VAR lt: vars){
				Policy.LVARRecord.put(lt._sType, lt._sVarName);
				Policy.TYPERecord.put(lt._sVarName, lt._sType);
			}
		}
		else{
			if(e instanceof AGG_EXPR){
				ArrayList<LTYPED_VAR> vars = ((AGG_EXPR) e)._alVariables;
				for(LTYPED_VAR lt: vars){
					Policy.LVARRecord.put(lt._sType, lt._sVarName);
					Policy.TYPERecord.put(lt._sVarName, lt._sType);
				}
			}
		}
	}
	
	public ArrayList<ArrayList<Integer>> FindSubs(int coeff, HashMap<LVAR, RDDL.LTERM> subs, EXPR c, HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>> m) throws Exception {
		ArrayList<ArrayList<Integer>> res = new ArrayList<>();
		res.add(new ArrayList<>());
		res.add(new ArrayList<>());
		if(c instanceof OPER_EXPR) {
			OPER_EXPR operC = (OPER_EXPR)c;
			if(operC._op.equals(OPER_EXPR.TIMES) && ((OPER_EXPR)c)._e1 instanceof RDDL.INT_CONST_EXPR && ((OPER_EXPR)c)._e2 instanceof PVAR_EXPR) {
				res = FindSubs(((RDDL.INT_CONST_EXPR)((OPER_EXPR)c)._e1)._nValue, subs, operC._e2, m);
			}
			else {
				if(!operC._op.equals(OPER_EXPR.PLUS)) {
					throw new Exception("FindSubs: only supports +/sum/pvar");
				}
				else {
					res = FindSubs(1, subs, operC._e1, m);
					ArrayList<ArrayList<Integer>> newRes = FindSubs(1, subs, operC._e2, m);
					res.get(0).addAll(newRes.get(0));
					res.get(1).addAll(newRes.get(1));
				}
			}
		}
		else {
			if(c instanceof AGG_EXPR) {
				AGG_EXPR aggC = (AGG_EXPR)c;
				if(!aggC._op.equals(AGG_EXPR.SUM)) {
					throw new Exception("FindSubs: only supports +/sum/pvar");
				}
				//System.out.println("VARS: " + _alVariables);
				ArrayList<ArrayList<LCONST>> possible_subs = generateAtoms(aggC._alVariables);
				// Evaluate all possible substitutions
				for (ArrayList<LCONST> sub_inst : possible_subs) {
					HashMap<LVAR, RDDL.LTERM> newSubs = new HashMap<>();
					newSubs.putAll(subs);
					for (int i = 0; i < aggC._alVariables.size(); i++) {
						newSubs.put(aggC._alVariables.get(i)._sVarName, sub_inst.get(i));
					}
					ArrayList<ArrayList<Integer>> newRes = FindSubs(1, newSubs, aggC._e, m);
					res.get(0).addAll(newRes.get(0));
					res.get(1).addAll(newRes.get(1));
				}
			}
			else {
				if(c instanceof PVAR_EXPR) {
					PVAR_EXPR pvarC = (PVAR_EXPR)c;
					ArrayList<LCONST> terms = new ArrayList<>();
					for(RDDL.LTERM l: pvarC._alTerms) {
						terms.add((LCONST)subs.get(l));
					}
					res.get(0).add(m.get(pvarC._pName).get(terms).term.var);
					res.get(1).add(coeff);
				}
				else {
					throw new Exception("FindSubs: only supports +/sum/pvar");
				}
			}
		}
		return res;
	}

	public ArrayList<TYPE_NAME> LCONST2TYPE_NAME(ArrayList<LCONST> consts, HashMap<LCONST, LVAR> vars) {
		ArrayList<LVAR> lvs = new ArrayList<>();
		ArrayList<TYPE_NAME> tynames = new ArrayList<>();
		for(LCONST l: consts) {
			lvs.add(vars.get(l));
		}
		for(LVAR lv: lvs) {
			tynames.add(Policy.TYPERecord.get(lv));
		}
		return tynames;
	}
	
	public void AddExtraActionEff(HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>> m, 
			ArrayList<ArrayList<Integer>> sumVars , ArrayList<Integer> sumLimit, ArrayList<EXPR> sumLimitExpr, ArrayList<ArrayList<Integer>> sumcoe) throws Exception{
		
		//deals with different constrints
		for(BOOL_EXPR c: _alActionPreconditions){
			
			
			if(c instanceof CONN_EXPR) {
				//move() => xx
				if(((CONN_EXPR) c)._sConn.equals("=>")) {
					CONN_EXPR conn = (CONN_EXPR)c;
					// forall_{move() => XXXXXXX}
					if(conn._alSubNodes.get(0) instanceof PVAR_EXPR){
						PVAR_EXPR theExp = (PVAR_EXPR)(conn._alSubNodes.get(0));
						PVAR_NAME theP = theExp._pName;
						//type name list is empty
						ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
						if(_alActionNames.contains(theP)){
							if(!Policy._extraEffects.containsKey(theP)){
								Policy._extraEffects.put(theP, new HashMap<>());
							}
							if(!Policy._extraEffects.get(theP).containsKey(theTypes)) {
								Policy._extraEffects.get(theP).put(theTypes, new ArrayList<>());
							}
							Policy._extraEffects.get(theP).get(theTypes).add(conn._alSubNodes.get(1));	
							//record the lvars used in the action preconditions
							//this is to verify that the action variable being evaluated has the same lvars
							//as in the constraints
							//would be called when adding the effects to the action variables
							if(!Policy._extraEffectsLVARS.containsKey(theP)){
								Policy._extraEffectsLVARS.put(theP, new HashMap<>());
							}
							if(!Policy._extraEffectsLVARS.get(theP).containsKey(theTypes)) {
								Policy._extraEffectsLVARS.get(theP).put(theTypes, new ArrayList<>());
							}
							Policy._extraEffectsLVARS.get(theP).put(theTypes, theExp._alTerms);	
							continue;
						}
					}
				}
				
				// xxxx|exists
				if(((CONN_EXPR) c)._sConn.equals("|")) {
					CONN_EXPR conn = (CONN_EXPR)c;
					// forall_{move() => XXXXXXX}
					if(conn._alSubNodes.get(0) instanceof PVAR_EXPR && conn._alSubNodes.get(1) instanceof QUANT_EXPR){
						UpdateRecord((QUANT_EXPR)conn._alSubNodes.get(1));
						PVAR_EXPR leftExp = (PVAR_EXPR)(conn._alSubNodes.get(0));
						PVAR_NAME leftP = leftExp._pName;
						QUANT_EXPR theExist = (QUANT_EXPR)conn._alSubNodes.get(1);
						if(theExist._sQuantType.equals("exists") && theExist._expr instanceof PVAR_EXPR) {
							PVAR_EXPR rightExp = (PVAR_EXPR)theExist._expr;
							PVAR_NAME rightP = rightExp._pName;
							//type name list is empty
							if(_alActionNames.contains(leftP) && _alActionNames.contains(rightP)){
								ArrayList<TYPE_NAME> rightTypes = new ArrayList<>();
								for(LTERM l: rightExp._alTerms) {
									rightTypes.add(Policy.TYPERecord.get(l));
								}
								
								if (!Policy._forceActionCondExist.containsKey(rightP)) {
									Policy._forceActionCondExist.put(rightP, new HashMap<>());
								}
								if (!Policy._forceActionCondExist.get(rightP).containsKey(rightTypes)) {
									Policy._forceActionCondExist.get(rightP).put(rightTypes, new ArrayList<>());
								}
								Policy._forceActionCondExist.get(rightP).get(rightTypes).add(1.0);
								// record the lvars used in the action preconditions
								// this is to verify that the action variable being evaluated has the same lvars
								// as in the constraints
								// would be called when adding the effects to the action variables
								if (!Policy._forcedCondExistLVARS.containsKey(rightP)) {
									Policy._forcedCondExistLVARS.put(rightP, new HashMap<>());
								}
								if (!Policy._forcedCondExistLVARS.get(rightP).containsKey(rightTypes)) {
									Policy._forcedCondExistLVARS.get(rightP).put(rightTypes, new ArrayList<>());
								}
								Policy._forcedCondExistLVARS.get(rightP).put(rightTypes, rightExp._alTerms);
								
								ArrayList<TYPE_NAME> leftTypes = new ArrayList<>();
								for(LTERM l: leftExp._alTerms) {
									leftTypes.add(Policy.TYPERecord.get(l));
								}
								
								if (!Policy._forceActionCondExist.containsKey(leftP)) {
									Policy._forceActionCondExist.put(leftP, new HashMap<>());
								}
								if (!Policy._forceActionCondExist.get(leftP).containsKey(leftTypes)) {
									Policy._forceActionCondExist.get(leftP).put(leftTypes, new ArrayList<>());
								}
								Policy._forceActionCondExist.get(leftP).get(leftTypes).add(1.0);
								// record the lvars used in the action preconditions
								// this is to verify that the action variable being evaluated has the same lvars
								// as in the constraints
								// would be called when adding the effects to the action variables
								if (!Policy._forcedCondExistLVARS.containsKey(leftP)) {
									Policy._forcedCondExistLVARS.put(leftP, new HashMap<>());
								}
								if (!Policy._forcedCondExistLVARS.get(leftP).containsKey(leftTypes)) {
									Policy._forcedCondExistLVARS.get(leftP).put(leftTypes, new ArrayList<>());
								}
								Policy._forcedCondExistLVARS.get(leftP).put(leftTypes, leftExp._alTerms);
								continue;		
							}
						}
					}
				}
				
				// exists_{move()}|xxxxxx
				if(((CONN_EXPR) c)._sConn.equals("|")) {
					CONN_EXPR conn = (CONN_EXPR)c;
					// forall_{move() => XXXXXXX}
					if(conn._alSubNodes.get(1) instanceof PVAR_EXPR && conn._alSubNodes.get(0) instanceof QUANT_EXPR){
						UpdateRecord((QUANT_EXPR)conn._alSubNodes.get(0));
						PVAR_EXPR leftExp = (PVAR_EXPR)(conn._alSubNodes.get(1));
						PVAR_NAME leftP = leftExp._pName;
						QUANT_EXPR theExist = (QUANT_EXPR)conn._alSubNodes.get(0);
						if(theExist._sQuantType.equals("exists") && theExist._expr instanceof PVAR_EXPR) {
							PVAR_EXPR rightExp = (PVAR_EXPR)theExist._expr;
							PVAR_NAME rightP = rightExp._pName;
							//type name list is empty
							if(_alActionNames.contains(leftP) && _alActionNames.contains(rightP)){
								ArrayList<TYPE_NAME> rightTypes = new ArrayList<>();
								for(LTERM l: rightExp._alTerms) {
									rightTypes.add(Policy.TYPERecord.get(l));
								}
								
								if (!Policy._forceActionCondExist.containsKey(rightP)) {
									Policy._forceActionCondExist.put(rightP, new HashMap<>());
								}
								if (!Policy._forceActionCondExist.get(rightP).containsKey(rightTypes)) {
									Policy._forceActionCondExist.get(rightP).put(rightTypes, new ArrayList<>());
								}
								Policy._forceActionCondExist.get(rightP).get(rightTypes).add(1.0);
								// record the lvars used in the action preconditions
								// this is to verify that the action variable being evaluated has the same lvars
								// as in the constraints
								// would be called when adding the effects to the action variables
								if (!Policy._forcedCondExistLVARS.containsKey(rightP)) {
									Policy._forcedCondExistLVARS.put(rightP, new HashMap<>());
								}
								if (!Policy._forcedCondExistLVARS.get(rightP).containsKey(rightTypes)) {
									Policy._forcedCondExistLVARS.get(rightP).put(rightTypes, new ArrayList<>());
								}
								Policy._forcedCondExistLVARS.get(rightP).put(rightTypes, rightExp._alTerms);
								
								ArrayList<TYPE_NAME> leftTypes = new ArrayList<>();
								for(LTERM l: leftExp._alTerms) {
									leftTypes.add(Policy.TYPERecord.get(l));
								}
								
								if (!Policy._forceActionCondExist.containsKey(leftP)) {
									Policy._forceActionCondExist.put(leftP, new HashMap<>());
								}
								if (!Policy._forceActionCondExist.get(leftP).containsKey(leftTypes)) {
									Policy._forceActionCondExist.get(leftP).put(leftTypes, new ArrayList<>());
								}
								Policy._forceActionCondExist.get(leftP).get(leftTypes).add(1.0);
								// record the lvars used in the action preconditions
								// this is to verify that the action variable being evaluated has the same lvars
								// as in the constraints
								// would be called when adding the effects to the action variables
								if (!Policy._forcedCondExistLVARS.containsKey(leftP)) {
									Policy._forcedCondExistLVARS.put(leftP, new HashMap<>());
								}
								if (!Policy._forcedCondExistLVARS.get(leftP).containsKey(leftTypes)) {
									Policy._forcedCondExistLVARS.get(leftP).put(leftTypes, new ArrayList<>());
								}
								Policy._forcedCondExistLVARS.get(leftP).put(leftTypes, leftExp._alTerms);
								continue;
								
							}
						}
						
					}
				}
			}
			
			
			if(c instanceof QUANT_EXPR){
				UpdateRecord(c);
			}
			
			

			
			//move_1 + move_2 + ... <= xxx
			//(sum_{arguments} [move_1() + move_2 + ...] <= xxx)
			if(c instanceof COMP_EXPR) {
				ArrayList<ArrayList<Integer>> res = FindSubs(1, new HashMap<LVAR, RDDL.LTERM>(), 
						((COMP_EXPR) c)._e1, m);
				ArrayList<Integer> projectActions = res.get(0);
				sumVars.add(projectActions);
				sumcoe.add(res.get(1));
				for(int i = 0; i < projectActions.size(); i ++) {
					int theAct = projectActions.get(i);
					Policy.ifInSumConstraints[theAct] = true;
				}
				EXPR e2exp = ((COMP_EXPR)c)._e2;
				if(e2exp instanceof RDDL.INT_CONST_EXPR) {
					sumLimit.add(((RDDL.INT_CONST_EXPR)e2exp)._nValue);
					sumLimitExpr.add(null);
				}
				else {
					if(e2exp instanceof PVAR_EXPR) {
						PVAR_EXPR e2ExpPVAR = (PVAR_EXPR)((COMP_EXPR)c)._e2;
						sumLimit.add((Integer)getPVariableDefault(e2ExpPVAR._pName));
						sumLimitExpr.add(null);
					}
					else {
						if(e2exp instanceof AGG_EXPR) {
							sumLimitExpr.add(e2exp);
						}
						else {
							throw new EvalException("Compare expr only supports <= INT/sum_{}");
						}
					}
				}
				if(((COMP_EXPR) c)._comp.equals("==")) {
					Policy.ifEqual.add(true);
				}
				else {
					Policy.ifEqual.add(false);
				}
				continue;
			}
			
			
			if(c instanceof QUANT_EXPR && ((QUANT_EXPR)c)._sQuantType.equals("forall")){
				BOOL_EXPR theE = ((QUANT_EXPR) c)._expr;
				if(theE instanceof CONN_EXPR){	
					if(((CONN_EXPR) theE)._sConn.equals("=>")) {
						CONN_EXPR conn = (CONN_EXPR)theE;
						// forall_{move() => XXXXXXX}
						if(conn._alSubNodes.get(0) instanceof PVAR_EXPR){
							PVAR_EXPR theExp = (PVAR_EXPR)(conn._alSubNodes.get(0));
							PVAR_NAME theP = theExp._pName;
							ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
							for(LTERM l: theExp._alTerms) {
								theTypes.add(Policy.TYPERecord.get(l));
							}
							if(_alActionNames.contains(theP)){
								if(!Policy._extraEffects.containsKey(theP)){
									Policy._extraEffects.put(theP, new HashMap<>());
								}
								if(!Policy._extraEffects.get(theP).containsKey(theTypes)) {
									Policy._extraEffects.get(theP).put(theTypes, new ArrayList<>());
								}
								Policy._extraEffects.get(theP).get(theTypes).add(conn._alSubNodes.get(1));	
								//record the lvars used in the action preconditions
								//this is to verify that the action variable being evaluated has the same lvars
								//as in the constraints
								//would be called when adding the effects to the action variables
								if(!Policy._extraEffectsLVARS.containsKey(theP)){
									Policy._extraEffectsLVARS.put(theP, new HashMap<>());
								}
								if(!Policy._extraEffectsLVARS.get(theP).containsKey(theTypes)) {
									Policy._extraEffectsLVARS.get(theP).put(theTypes, new ArrayList<>());
								}
								Policy._extraEffectsLVARS.get(theP).put(theTypes, theExp._alTerms);	
								continue;
							}
						}
						//forall_{move && XXX => XXXX} 
						if(conn._alSubNodes.get(0) instanceof CONN_EXPR){
							CONN_EXPR theExp = (CONN_EXPR)(conn._alSubNodes.get(0));
							if(theExp._sConn.equals("^") && theExp._alSubNodes.get(0) instanceof PVAR_EXPR && theExp._alSubNodes.get(1) instanceof PVAR_EXPR) {
								PVAR_EXPR var1 = (PVAR_EXPR)theExp._alSubNodes.get(0);
								PVAR_EXPR var2 = (PVAR_EXPR)theExp._alSubNodes.get(1);
								if(_alActionNames.contains(var1._pName) && !_alActionNames.contains(var2._pName)) {
									PVAR_NAME theP = var1._pName;
									ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
									for(LTERM l: var1._alTerms) {
										theTypes.add(Policy.TYPERecord.get(l));
									}
									if(_alActionNames.contains(theP)){
										if(!Policy._extraEffects.containsKey(theP)){
											Policy._extraEffects.put(theP, new HashMap<>());
										}
										if(!Policy._extraEffects.get(theP).containsKey(theTypes)) {
											Policy._extraEffects.get(theP).put(theTypes, new ArrayList<>());
										}
										QUANT_EXPR theConj = new QUANT_EXPR(((QUANT_EXPR)c)._sQuantType, ((QUANT_EXPR)c)._alVariables, ((QUANT_EXPR)c)._expr);
										Policy._extraEffects.get(theP).get(theTypes).add(theConj);
										//record the lvars used in the action preconditions
										//this is to verify that the action variable being evaluated has the same lvars
										//as in the constraints
										//would be called when adding the effects to the action variables
										if(!Policy._extraEffectsLVARS.containsKey(theP)){
											Policy._extraEffectsLVARS.put(theP, new HashMap<>());
										}
										if(!Policy._extraEffectsLVARS.get(theP).containsKey(theTypes)) {
											Policy._extraEffectsLVARS.get(theP).put(theTypes, new ArrayList<>());
										}
										Policy._extraEffectsLVARS.get(theP).put(theTypes, var1._alTerms);	
										continue;
									}
								}		
							}
						}
						
						// forall_{move() and cond() => XXXXXXX}
						if(conn._alSubNodes.get(0) instanceof CONN_EXPR){
							CONN_EXPR theExp = (CONN_EXPR)(conn._alSubNodes.get(0));
							if(theExp._sConn.equals("^") && theExp._alSubNodes.get(0) instanceof PVAR_EXPR && theExp._alSubNodes.get(1) instanceof PVAR_EXPR) {
								PVAR_EXPR var1 = (PVAR_EXPR)theExp._alSubNodes.get(1);
								PVAR_EXPR var2 = (PVAR_EXPR)theExp._alSubNodes.get(0);
								if(_alActionNames.contains(var1._pName) && !_alActionNames.contains(var2._pName)) {
									PVAR_NAME theP = var1._pName;
									ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
									for(LTERM l: var1._alTerms) {
										theTypes.add(Policy.TYPERecord.get(l));
									}
									if(_alActionNames.contains(theP)){
										if(!Policy._extraEffects.containsKey(theP)){
											Policy._extraEffects.put(theP, new HashMap<>());
										}
										if(!Policy._extraEffects.get(theP).containsKey(theTypes)) {
											Policy._extraEffects.get(theP).put(theTypes, new ArrayList<>());
										}
										QUANT_EXPR theConj = new QUANT_EXPR(((QUANT_EXPR)c)._sQuantType, ((QUANT_EXPR)c)._alVariables, ((QUANT_EXPR)c)._expr);
										
										((CONN_EXPR)theConj._expr)._alSubNodes.set(0, new PVAR_EXPR(var2._pName._sPVarName, var2._alTerms, var2._alMembers));
										Policy._extraEffects.get(theP).get(theTypes).add(theConj);
										//record the lvars used in the action preconditions
										//this is to verify that the action variable being evaluated has the same lvars
										//as in the constraints
										//would be called when adding the effects to the action variables
										if(!Policy._extraEffectsLVARS.containsKey(theP)){
											Policy._extraEffectsLVARS.put(theP, new HashMap<>());
										}
										if(!Policy._extraEffectsLVARS.get(theP).containsKey(theTypes)) {
											Policy._extraEffectsLVARS.get(theP).put(theTypes, new ArrayList<>());
										}
										Policy._extraEffectsLVARS.get(theP).put(theTypes, var1._alTerms);	
										continue;
									}
								}		
							}
						}
					}
				}
				
				
				
				if(theE instanceof COMP_EXPR) {
					//forall_{arguments} [sum_{}+sum_{} <= xx]
					try {
						HashMap<LVAR, RDDL.LTERM> subs = new HashMap<>();
						QUANT_EXPR quantC = (QUANT_EXPR) c;
						ArrayList<ArrayList<LCONST>> possible_subs = generateAtoms(quantC._alVariables);
						// Evaluate all possible substitutions
						for (ArrayList<LCONST> sub_inst : possible_subs) {
							for (int i = 0; i < quantC._alVariables.size(); i++) {
								subs.put(quantC._alVariables.get(i)._sVarName, sub_inst.get(i));
								ArrayList<ArrayList<Integer>> res = FindSubs(1, subs, ((COMP_EXPR) theE)._e1, m);
								ArrayList<Integer> projectActions = res.get(0);
								sumVars.add(projectActions);
								sumcoe.add(res.get(1));
								for(int j = 0; j < projectActions.size(); j ++) {
									int theAct = projectActions.get(j);
									if(theAct == 2) {
										int a = 1;
									}
									Policy.ifInSumConstraints[theAct] = true;
								}
								EXPR e2exp = ((COMP_EXPR)(((QUANT_EXPR) c)._expr))._e2;
								if(e2exp instanceof RDDL.INT_CONST_EXPR) {
									sumLimit.add(((RDDL.INT_CONST_EXPR)e2exp)._nValue);
									sumLimitExpr.add(null);
								}
								else {
									if(e2exp instanceof PVAR_EXPR) {
										PVAR_EXPR e2ExpPVAR = (PVAR_EXPR)((COMP_EXPR)(((QUANT_EXPR) c)._expr))._e2;
										sumLimit.add((Integer)getPVariableDefault(e2ExpPVAR._pName));
										sumLimitExpr.add(null);
									}
									else {
										throw new EvalException("Compare expr only supports <= INT");
									}
								}
								
								
								
								if(((COMP_EXPR) theE)._comp.equals("==")) {
									Policy.ifEqual.add(true);
								}
								else {
									Policy.ifEqual.add(false);
								}
							}
						}
					} catch (EvalException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					continue;
				}
				
				if(theE instanceof QUANT_EXPR && ((QUANT_EXPR)theE)._sQuantType.equals("forall")){
					UpdateRecord((QUANT_EXPR)theE);
					BOOL_EXPR theE2 = ((QUANT_EXPR) theE)._expr;
					if(theE2 instanceof CONN_EXPR){
						
						if(((CONN_EXPR) theE2)._sConn.equals("=>")) {
							CONN_EXPR conn = (CONN_EXPR)theE2;
							// forall_{move() => XXXXXXX}
							if(conn._alSubNodes.get(0) instanceof PVAR_EXPR){
								PVAR_EXPR theExp = (PVAR_EXPR)(conn._alSubNodes.get(0));
								PVAR_NAME theP = theExp._pName;
								ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
								for(LTERM l: theExp._alTerms) {
									theTypes.add(Policy.TYPERecord.get(l));
								}
								if(_alActionNames.contains(theP)){
									if(!Policy._extraEffects.containsKey(theP)){
										Policy._extraEffects.put(theP, new HashMap<>());
									}
									if(!Policy._extraEffects.get(theP).containsKey(theTypes)) {
										Policy._extraEffects.get(theP).put(theTypes, new ArrayList<>());
									}
									Policy._extraEffects.get(theP).get(theTypes).add(conn._alSubNodes.get(1));	
									//record the lvars used in the action preconditions
									//this is to verify that the action variable being evaluated has the same lvars
									//as in the constraints
									//would be called when adding the effects to the action variables
									if(!Policy._extraEffectsLVARS.containsKey(theP)){
										Policy._extraEffectsLVARS.put(theP, new HashMap<>());
									}
									if(!Policy._extraEffectsLVARS.get(theP).containsKey(theTypes)) {
										Policy._extraEffectsLVARS.get(theP).put(theTypes, new ArrayList<>());
									}
									Policy._extraEffectsLVARS.get(theP).put(theTypes, theExp._alTerms);	
									continue;
								}
							}
						}
					}
				}
			}
			
			// XXXXXX => forall_{move()}
			// XXXXXX => move
			if (c instanceof CONN_EXPR) {
				CONN_EXPR conn = ((CONN_EXPR) c);
				if((conn)._sConn.equals("=>")) {
					EXPR right = (conn)._alSubNodes.get(1);
					PVAR_EXPR thePVAR = null;
					if(right instanceof PVAR_EXPR) {
						thePVAR = (PVAR_EXPR)right;
					}
					else {
						if(right instanceof QUANT_EXPR && (((QUANT_EXPR)right)._sQuantType.equals("forall"))) {
							if (((QUANT_EXPR) right)._expr instanceof PVAR_EXPR) {
								thePVAR = (PVAR_EXPR)((QUANT_EXPR) right)._expr;
							}
						}
					}
					if(thePVAR != null) {
						PVAR_NAME theP = thePVAR._pName;

						ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
						for(LTERM l: thePVAR._alTerms) {
							theTypes.add(Policy.TYPERecord.get(l));
						}
						if (_alActionNames.contains(theP)) {
							if(!Policy._forceActionCondForall.containsKey(theP)){
								Policy._forceActionCondForall.put(theP, new HashMap<>());
							}
							if(!Policy._forceActionCondForall.get(theP).containsKey(theTypes)) {
								Policy._forceActionCondForall.get(theP).put(theTypes, new ArrayList<>());
							}
							Policy._forceActionCondForall.get(theP).get(theTypes).add(conn._alSubNodes.get(0));	
							//record the lvars used in the action preconditions
							//this is to verify that the action variable being evaluated has the same lvars
							//as in the constraints
							//would be called when adding the effects to the action variables
							if(!Policy._forcedCondForallLVARS.containsKey(theP)){
								Policy._forcedCondForallLVARS.put(theP, new HashMap<>());
							}
							if(!Policy._forcedCondForallLVARS.get(theP).containsKey(theTypes)) {
								Policy._forcedCondForallLVARS.get(theP).put(theTypes, new ArrayList<>());
							}
							Policy._forcedCondForallLVARS.get(theP).put(theTypes, thePVAR._alTerms);	
							continue;
						}
					}

				}
			} 
			
			
			if (c instanceof CONN_EXPR) {
				CONN_EXPR conn = ((CONN_EXPR) c);
				if((conn)._sConn.equals("=>")) {
					EXPR right = (conn)._alSubNodes.get(1);
					PVAR_EXPR thePVAR = null;
					
					if (right instanceof QUANT_EXPR && (((QUANT_EXPR) right)._sQuantType.equals("exists"))) {
						if (((QUANT_EXPR) right)._expr instanceof PVAR_EXPR) {
							thePVAR = (PVAR_EXPR) ((QUANT_EXPR) right)._expr;
						}
					}
					
					if(thePVAR != null) {
						PVAR_NAME theP = thePVAR._pName;

						ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
						for(LTERM l: thePVAR._alTerms) {
							theTypes.add(Policy.TYPERecord.get(l));
						}
						if (_alActionNames.contains(theP)) {
							if(!Policy._forceActionCondExist.containsKey(theP)){
								Policy._forceActionCondExist.put(theP, new HashMap<>());
							}
							if(!Policy._forceActionCondExist.get(theP).containsKey(theTypes)) {
								Policy._forceActionCondExist.get(theP).put(theTypes, new ArrayList<>());
							}
							Policy._forceActionCondExist.get(theP).get(theTypes).add(conn._alSubNodes.get(0));	
							//record the lvars used in the action preconditions
							//this is to verify that the action variable being evaluated has the same lvars
							//as in the constraints
							//would be called when adding the effects to the action variables
							if(!Policy._forcedCondExistLVARS.containsKey(theP)){
								Policy._forcedCondExistLVARS.put(theP, new HashMap<>());
							}
							if(!Policy._forcedCondExistLVARS.get(theP).containsKey(theTypes)) {
								Policy._forcedCondExistLVARS.get(theP).put(theTypes, new ArrayList<>());
							}
							Policy._forcedCondExistLVARS.get(theP).put(theTypes, thePVAR._alTerms);	
							continue;
						}
					}

				}
			} 
			
			//xxxx=>act1|act2|...
			if (c instanceof CONN_EXPR) {
				CONN_EXPR conn = ((CONN_EXPR) c);
				if((conn)._sConn.equals("=>")) {
					EXPR right = (conn)._alSubNodes.get(1);
					ArrayList<PVAR_EXPR> thePVARs = new ArrayList<>();
					
					if (right instanceof CONN_EXPR && (((CONN_EXPR) right)._sConn.equals("|"))) {
						boolean ifDealwith = true;
						for(EXPR theSub: ((CONN_EXPR) right)._alSubNodes) {
							if(!(theSub instanceof PVAR_EXPR) || !_alActionNames.contains(((PVAR_EXPR)theSub)._pName)) {
								ifDealwith = false;
								break;
							}
							else {
								thePVARs.add((PVAR_EXPR)theSub);
							}
						}
						if(ifDealwith) {
							for(PVAR_EXPR thePVAR: thePVARs) {
								PVAR_NAME theP = thePVAR._pName;

								ArrayList<TYPE_NAME> theTypes = new ArrayList<>();
								for(LTERM l: thePVAR._alTerms) {
									theTypes.add(Policy.TYPERecord.get(l));
								}
								if (_alActionNames.contains(theP)) {
									if(!Policy._forceActionCondExist.containsKey(theP)){
										Policy._forceActionCondExist.put(theP, new HashMap<>());
									}
									if(!Policy._forceActionCondExist.get(theP).containsKey(theTypes)) {
										Policy._forceActionCondExist.get(theP).put(theTypes, new ArrayList<>());
									}
									Policy._forceActionCondExist.get(theP).get(theTypes).add(conn._alSubNodes.get(0));	
									//record the lvars used in the action preconditions
									//this is to verify that the action variable being evaluated has the same lvars
									//as in the constraints
									//would be called when adding the effects to the action variables
									if(!Policy._forcedCondExistLVARS.containsKey(theP)){
										Policy._forcedCondExistLVARS.put(theP, new HashMap<>());
									}
									if(!Policy._forcedCondExistLVARS.get(theP).containsKey(theTypes)) {
										Policy._forcedCondExistLVARS.get(theP).put(theTypes, new ArrayList<>());
									}
									Policy._forcedCondExistLVARS.get(theP).put(theTypes, thePVAR._alTerms);	
									
								}
							}
							continue;
						}
					}
				}
			} 
			
			
			throw new Exception ("The constraint: " + c + " is not supported yet!");
			
			//Policy._ifDisAction = true;
			//break;
		}
	}
	
	public void CalActionDiscount(){
		
		TreeExp theDis = TreeExp.BuildNewTreeExp(1.0, null);
		for(BOOL_EXPR theCons: _alActionPreconditions){
			try {
				theDis = theDis.TIMES(toTExp(theCons.sample(new HashMap<LVAR, LCONST>(), this, new RandomDataGenerator()), null));
			} catch (EvalException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		//Policy._actionDiscount = null;
		//Policy._actionDiscount = theDis;
	}
	
	public ArrayList<ArrayList<LCONST>> generateAtoms(PVAR_NAME p) throws EvalException {
		ArrayList<ArrayList<LCONST>> list = new ArrayList<ArrayList<LCONST>>();
		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
		//System.out.print("Generating pvars for " + pvar_def + ": ") ;
		if (pvar_def == null) {
			System.out.println("Error, could not generate atoms for unknown variable name.");
			new Exception().printStackTrace();
		}
		generateAtoms(pvar_def, 0, new ArrayList<LCONST>(), list);
		//System.out.println(list);
		return list;
	}
	
	private void generateAtoms(PVARIABLE_DEF pvar_def, int index, 
			ArrayList<LCONST> cur_assign, ArrayList<ArrayList<LCONST>> list) throws EvalException {
		if (index >= pvar_def._alParamTypes.size()) {
			// No more indices to generate
			list.add(cur_assign);
		} else {
			// Get the object list for this index
			TYPE_NAME type = pvar_def._alParamTypes.get(index);
			ArrayList<LCONST> objects = _hmObject2Consts.get(type);
			if (objects == null)
				throw new EvalException("ERROR: could not find definition of object type '" + type + "'\nwhen instantiating " + pvar_def);
			for (LCONST obj : objects) {
				ArrayList<LCONST> new_assign = (ArrayList<LCONST>)cur_assign.clone();
				new_assign.add(obj);
				generateAtoms(pvar_def, index+1, new_assign, list);
			}
		}
	}
	
	public ArrayList<ArrayList<LCONST>> generateAtoms(ArrayList<LTYPED_VAR> tvar_list) {
		ArrayList<ArrayList<LCONST>> list = new ArrayList<ArrayList<LCONST>>();
		generateAtoms(tvar_list, 0, new ArrayList<LCONST>(), list);
		return list;
	}
	
	private void generateAtoms(ArrayList<LTYPED_VAR> tvar_list, int index, 
			ArrayList<LCONST> cur_assign, ArrayList<ArrayList<LCONST>> list) {
		if (index >= tvar_list.size()) {
			// No more indices to generate
			list.add(cur_assign);
		} else {
			// Get the object list for this index
			TYPE_NAME type = tvar_list.get(index)._sType;
			ArrayList<LCONST> objects = _hmObject2Consts.get(type);
			if (objects == null) {
				System.out.println("Object type '" + type + "' did not have any objects or enumerated values defined.");
			}
			//System.out.println(type + " : " + objects);
			for (LCONST obj : objects) {
				ArrayList<LCONST> new_assign = (ArrayList<LCONST>)cur_assign.clone();
				new_assign.add(obj);
				generateAtoms(tvar_list, index+1, new_assign, list);
			}
		}
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		// Go through all variable types (state, interm, observ, action, nonfluent)
		for (Map.Entry<String,ArrayList<PVAR_NAME>> e : _hmTypeMap.entrySet()) {
			
			if (e.getKey().equals("nonfluent"))
				continue;
			
			// Go through all variable names p for a variable type
			for (PVAR_NAME p : e.getValue()) 
				try {
					// Go through all term groundings for variable p
					PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
					boolean derived = (pvar_def instanceof PVARIABLE_INTERM_DEF) && ((PVARIABLE_INTERM_DEF)pvar_def)._bDerived;
					
					ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);										
					for (ArrayList<LCONST> gfluent : gfluents)
						sb.append("- " + (derived ? "derived" : e.getKey()) + ": " + p + 
								(gfluent.size() > 0 ? gfluent : "") + " := " + 
								getPVariableAssign(p, gfluent) + "\n");
						
				} catch (EvalException ex) {
				}
		}
				
		return sb.toString();
	}


}
