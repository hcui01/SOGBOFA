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

import java.io.Serializable;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.Map.Entry;

import javax.swing.plaf.basic.BasicSliderUI.ActionScroller;

import rddl.RDDL.BOOL_EXPR;
import rddl.RDDL.CPF_DEF;
import rddl.RDDL.DOMAIN;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.ENUM_VAL;
import rddl.RDDL.EXPR;
import rddl.RDDL.LCONST;
import rddl.RDDL.LTYPED_VAR;
import rddl.RDDL.LVAR;
import rddl.RDDL.OBJECTS_DEF;
import rddl.RDDL.PVARIABLE_ACTION_DEF;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVARIABLE_INTERM_DEF;
import rddl.RDDL.PVARIABLE_OBS_DEF;
import rddl.RDDL.PVARIABLE_STATE_DEF;
import rddl.RDDL.PVAR_EXPR;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import rddl.RDDL.TYPE_DEF;
import rddl.RDDL.TYPE_NAME;
import rddl.policy.DeepCloneUtil;
import rddl.policy.RandomConcurrentPolicyIndex;
import util.Pair;

public class AState implements Cloneable, Serializable{
	public AState(){
		
	}
	
	public final boolean DISPLAY_UPDATES = false;
	
	public final int UNDEFINED = 0;
	public final int STATE     = 1;
	public final int NONFLUENT = 2;
	public final int ACTION    = 3;
	public final int INTERM    = 4;
	public final int OBSERV    = 5;
	
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
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> _state;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> _nonfluents;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> _actions;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>> _interm;
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>> _observ;

	// Constraints
	public ArrayList<BOOL_EXPR> _alConstraints;
	public EXPR _reward;
	public int _nMaxNondefActions = -1;
	
	public Object clone()    
    {    
        Object o=null;    
       try    
        {    
        o=(AState)super.clone();//Object 中的clone()识别出你要复制的是哪一个对象。    
        }    
       catch(CloneNotSupportedException e)    
        {    
            System.out.println(e.toString());    
        }    
       return o;    
    }    
	
	// Temporarily holds next state while it is being computed
	public HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> _nextState;

	public void init(State s) throws EvalException {
		
		_hmPVariables = s._hmPVariables;
		_hmTypes = s._hmTypes;
		_hmCPFs = s._hmCPFs;
		_alConstraints = s._alConstraints;
		_reward = s._reward;
		_nMaxNondefActions = s._nMaxNondefActions;
		
		// Map object class name to list
		_hmObject2Consts = new HashMap<TYPE_NAME,ArrayList<LCONST>>();
		for (Map.Entry<TYPE_NAME,ArrayList<LCONST>> o2c : s._hmObject2Consts.entrySet()) {
			_hmObject2Consts.put(o2c.getKey(), o2c.getValue());
		}


		// Initialize assignments (missing means default)
		_state      = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		_interm     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_nextState  = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		_observ     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_actions    = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		_nonfluents = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();

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
				_state.put(pname, new HashMap<ArrayList<LCONST>,Double>());
				_nextState.put(pname, new HashMap<ArrayList<LCONST>,Double>());
			} else if (def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alNonFluentNames.add(pname);
				_nonfluents.put(pname, new HashMap<ArrayList<LCONST>,Double>());
			} else if (def instanceof PVARIABLE_ACTION_DEF) {
				_alActionNames.add(pname);
				_actions.put(pname, new HashMap<ArrayList<LCONST>,Double>());
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
	
	public void init(AState s) throws EvalException {
		
		_hmPVariables = s._hmPVariables;
		_hmTypes = s._hmTypes;
		_hmCPFs = s._hmCPFs;
		_alConstraints = s._alConstraints;
		_reward = s._reward;
		_nMaxNondefActions = s._nMaxNondefActions;
		
		// Map object class name to list
		_hmObject2Consts = new HashMap<TYPE_NAME,ArrayList<LCONST>>();
		for (Map.Entry<TYPE_NAME,ArrayList<LCONST>> o2c : s._hmObject2Consts.entrySet()) {
			_hmObject2Consts.put(o2c.getKey(), o2c.getValue());
		}


		// Initialize assignments (missing means default)
		_state      = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		_interm     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_nextState  = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		_observ     = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>>();
		_actions    = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		_nonfluents = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();

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
				_state.put(pname, new HashMap<ArrayList<LCONST>,Double>());
				_nextState.put(pname, new HashMap<ArrayList<LCONST>,Double>());
			} else if (def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)def)._bNonFluent) {
				_alNonFluentNames.add(pname);
				_nonfluents.put(pname, new HashMap<ArrayList<LCONST>, Double>());
			} else if (def instanceof PVARIABLE_ACTION_DEF) {
				_alActionNames.add(pname);
				_actions.put(pname, new HashMap<ArrayList<LCONST>,Double>());
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

	public void init(HashMap<TYPE_NAME,OBJECTS_DEF> nonfluent_objects,
			 HashMap<TYPE_NAME,OBJECTS_DEF> instance_objects,
			 HashMap<TYPE_NAME,TYPE_DEF> typedefs,
			 HashMap<PVAR_NAME,PVARIABLE_DEF> pvariables,
			 HashMap<PVAR_NAME,CPF_DEF> cpfs,
			 ArrayList<PVAR_INST_DEF> init_state,
			 ArrayList<PVAR_INST_DEF> nonfluents,
			 ArrayList<BOOL_EXPR> state_action_constraints,
			 EXPR reward, 
			 int max_nondef_actions) throws EvalException {

		_hmPVariables = pvariables;
		_hmTypes = typedefs;
		_hmCPFs = cpfs;
		_alConstraints = state_action_constraints;
		_reward = reward;
		_nMaxNondefActions = max_nondef_actions;

		// Map object class name to list
		_hmObject2Consts = new HashMap<TYPE_NAME, ArrayList<LCONST>>();
		if (nonfluent_objects != null)
			for (OBJECTS_DEF obj_def : nonfluent_objects.values())
				_hmObject2Consts.put(obj_def._sObjectClass, obj_def._alObjects);
		if (instance_objects != null)
			for (OBJECTS_DEF obj_def : instance_objects.values())
				_hmObject2Consts.put(obj_def._sObjectClass, obj_def._alObjects);
		for (Map.Entry<TYPE_NAME, TYPE_DEF> e : typedefs.entrySet()) {
			if (e.getValue() instanceof ENUM_TYPE_DEF) {
				ENUM_TYPE_DEF etd = (ENUM_TYPE_DEF) e.getValue();
				ArrayList<LCONST> values = new ArrayList<LCONST>();
				for (ENUM_VAL v : etd._alPossibleValues)
					values.add(v);
				_hmObject2Consts.put(etd._sName, values);
			}
		}

		// Initialize assignments (missing means default)
		_state = new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Double>>();
		_interm = new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Object>>();
		_nextState = new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Double>>();
		_observ = new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Object>>();
		_actions = new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Double>>();
		_nonfluents = new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Double>>();

		// Initialize variable lists
		_alStateNames.clear();
		_alNonFluentNames.clear();
		_alActionNames.clear();
		_alObservNames.clear();
		_alIntermNames.clear();
		for (Map.Entry<PVAR_NAME, PVARIABLE_DEF> e : _hmPVariables.entrySet()) {
			PVAR_NAME pname = e.getKey();
			PVARIABLE_DEF def = e.getValue();
			if (def instanceof PVARIABLE_STATE_DEF
					&& !((PVARIABLE_STATE_DEF) def)._bNonFluent) {
				_alStateNames.add(pname);
				_state.put(pname, new HashMap<ArrayList<LCONST>, Double>());
				_nextState.put(pname, new HashMap<ArrayList<LCONST>, Double>());
			} else if (def instanceof PVARIABLE_STATE_DEF
					&& ((PVARIABLE_STATE_DEF) def)._bNonFluent) {
				_alNonFluentNames.add(pname);
				_nonfluents
						.put(pname, new HashMap<ArrayList<LCONST>, Double>());
			} else if (def instanceof PVARIABLE_ACTION_DEF) {
				_alActionNames.add(pname);
				_actions.put(pname, new HashMap<ArrayList<LCONST>, Double>());
			} else if (def instanceof PVARIABLE_OBS_DEF) {
				_alObservNames.add(pname);
				_observ.put(pname, new HashMap<ArrayList<LCONST>, Object>());
			} else if (def instanceof PVARIABLE_INTERM_DEF) {
				_alIntermNames.add(pname);
				_tmIntermNames.put(new Pair(
						((PVARIABLE_INTERM_DEF) def)._nLevel, pname), pname);
				_interm.put(pname, new HashMap<ArrayList<LCONST>, Object>());
			}
		}
		_hmTypeMap.put("states", _alStateNames);
		_hmTypeMap.put("nonfluent", _alNonFluentNames);
		_hmTypeMap.put("action", _alActionNames);
		_hmTypeMap.put("observ", _alObservNames);
		_hmTypeMap.put("interm", _alIntermNames);

		// Set initial state and pvariables
		setPVariables(_state, init_state);
		if (nonfluents != null)
			setPVariables(_nonfluents, nonfluents);
	}

	// translat object to double
	// only supports int, bool
	public double getDouble(Object o) throws EvalException {
		if (o instanceof ENUM_VAL) {
			throw new EvalException("enum not supported");
		}
		if (o instanceof Boolean) {
			return (Boolean) o ? 1.0 : 0.0;
		} else if (o instanceof Integer) {
			return Double.valueOf(o.toString());
		} else {
			return (Double) o;
		}
		
	}
	
	//from normal initial state to aggregate initial state
	//only support boolean state variable now
	//partially completed; only non-default value is dealt
	public boolean InitAggState(State initS) throws EvalException {
	
		Iterator outer = initS._state.entrySet().iterator(); 
		while (outer.hasNext()) { 
		    Map.Entry entry = (Map.Entry) outer.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Object> val = (HashMap<ArrayList<LCONST>, Object>)entry.getValue(); 
		    Iterator inner = val.entrySet().iterator();
		    HashMap<ArrayList<LCONST>, Double> pred_assign = _state.get(key);
		    while (inner.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    double theValue = getDouble(entry2.getValue()); 
			    pred_assign.put(theTerm, theValue);
			} 
		} 
		Iterator outer2 = initS._nonfluents.entrySet().iterator(); 
		while (outer2.hasNext()) { 
		    Map.Entry entry = (Map.Entry) outer2.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Object> val = (HashMap<ArrayList<LCONST>, Object>)entry.getValue(); 
		    Iterator inner2 = val.entrySet().iterator();
		    HashMap<ArrayList<LCONST>, Double> pred_assign = _nonfluents.get(key);
		    while (inner2.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner2.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    double theValue = getDouble(entry2.getValue()); 
			    pred_assign.put(theTerm, theValue);
			} 
		} 
		return true;
		
	}

	public boolean InitAggState(AState initS) throws EvalException {
		
		Iterator outer = initS._state.entrySet().iterator(); 
		while (outer.hasNext()) { 
		    Map.Entry entry = (Map.Entry) outer.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Double> val = (HashMap<ArrayList<LCONST>, Double>)entry.getValue(); 
		    Iterator inner = val.entrySet().iterator();
		    HashMap<ArrayList<LCONST>, Double> pred_assign = _state.get(key);
		    while (inner.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    double theValue = (Double)entry2.getValue(); 
			    pred_assign.put(theTerm, theValue);
			} 
		} 
		Iterator outer2 = initS._nonfluents.entrySet().iterator(); 
		while (outer2.hasNext()) { 
		    Map.Entry entry = (Map.Entry) outer2.next(); 
		    PVAR_NAME key = (PVAR_NAME)entry.getKey(); 
		    HashMap<ArrayList<LCONST>, Double> val = (HashMap<ArrayList<LCONST>, Double>)entry.getValue(); 
		    Iterator inner2 = val.entrySet().iterator();
		    HashMap<ArrayList<LCONST>, Double> pred_assign = _nonfluents.get(key);
		    while (inner2.hasNext()) { 
			    Map.Entry entry2 = (Map.Entry) inner2.next(); 
			    ArrayList<LCONST> theTerm = (ArrayList<LCONST>)entry2.getKey(); 
			    double theValue = (Double)entry2.getValue(); 
			    pred_assign.put(theTerm, theValue);
			} 
		} 
		return true;
	}
	
	//restore astate from another astate
	//only deal with _state
	public boolean RestoreAState(AState ori) throws EvalException{
		for(PVAR_NAME p : _alStateNames){
			HashMap<ArrayList<LCONST>, Double> ori_state = ori._state.get(p);
			//HashMap<ArrayList<LCONST>, Double> ori_nextState = ori._nextState.;
			HashMap<ArrayList<LCONST>, Double> des_state = _state.get(p);
			ArrayList<ArrayList<LCONST>> terms = generateAtoms(p);
			for(ArrayList<LCONST> term : terms){
				des_state.put(term, ori_state.get(term));
			}
		}
		return true;
	}
	
	//return a double representing availability
	public double checkStateActionConstraints(ArrayList<PVAR_INST_DEF> actions)  
	
		throws EvalException {
		
		//throw new EvalException("state-action constraints not supported yet in agg state");
		
		
		// Clear then set the actions
		for (PVAR_NAME p : _actions.keySet())
			_actions.get(p).clear();
		setActions(actions);

		// Check state-action constraints
		HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
		double availability = 1.0;
		for (BOOL_EXPR constraint : _alConstraints) {
			// satisfied must be true if get here
			availability *= (Double)constraint.sample(subs, this, null);
			if( availability == 0 ){
				break;
			}
		}
		return availability;
	}
	
	public void setActions(ArrayList<PVAR_INST_DEF> actions) throws EvalException{
		
		for(PVAR_NAME act : _alActionNames){
			ArrayList<ArrayList<LCONST>> terms = generateAtoms(act);
			PVARIABLE_DEF pvar_def = _hmPVariables.get(act);
			Object def_value = ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;
			for(ArrayList<LCONST> term : terms){
				_actions.get(act).put(term, getDouble(def_value));
			}
		}
		
		boolean fatal_error = false;
		for (PVAR_INST_DEF def : actions) {
			
			// Get the assignments for this PVAR
			HashMap<ArrayList<LCONST>,Double> pred_assign = _actions.get(def._sPredName);
			if (pred_assign == null) {
				System.out.println("FATAL ERROR: '" + def._sPredName + "' not defined");
				fatal_error = true;
			}
			
			// Get default value if it exists
			Object def_value = null;
			PVARIABLE_DEF pvar_def = _hmPVariables.get(def._sPredName);
			def_value = ((PVARIABLE_ACTION_DEF)pvar_def)._oDefValue;
			pred_assign.put(def._alTerms, getDouble(def_value));
			// Set value if non-default
			if (def_value != null && !def_value.equals(def._oValue)) {
				pred_assign.put(def._alTerms, getDouble(def._oValue));
			}
		}
		
		if (fatal_error) {
			System.out.println("ABORTING DUE TO FATAL ERRORS");
			System.exit(1);
		}
	}
	
	public double computeNextStateByRoll(DOMAIN domain, ArrayList<PVAR_INST_DEF> actions, Random r, State cs, boolean ifTop, int k) throws EvalException{
		
		if(ifTop){
			computeNextState(actions, r);
			return ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
					cs, r)).doubleValue();
		}
		else{
			double reward = 0;
			_nextState.clear();
			State ts = new State();
			ts = (State) DeepCloneUtil.deepClone(cs);
			
			//get assignments for each _state variable
			HashMap<PVAR_INST_DEF, Double> bitProb = new HashMap<RDDL.PVAR_INST_DEF, Double>();
//			System.out.println(s);
			for(int i = 1; i <= k; i ++){
				Iterator<Entry<PVAR_NAME, HashMap<ArrayList<LCONST>, Double>>> levelOneIter = _state.entrySet().iterator(); 
				while (levelOneIter.hasNext()){
					Map.Entry entry = (Map.Entry)levelOneIter.next();
					HashMap<ArrayList<LCONST>, Double> levelTwoMapping = (HashMap<ArrayList<LCONST>, Double>)entry.getValue();
					PVAR_NAME theName = (PVAR_NAME)entry.getKey();
					Iterator<Entry<ArrayList<LCONST>, Double>> levelTwoIter = levelTwoMapping.entrySet().iterator();
					while(levelTwoIter.hasNext()){
						Map.Entry levelTwoEntry = (Map.Entry)levelTwoIter.next();
						Double theProb = (Double)levelTwoEntry.getValue();
						ArrayList<LCONST> thePars = (ArrayList<RDDL.LCONST>)levelTwoEntry.getKey();
						double dice = r.nextDouble();
						HashMap<ArrayList<LCONST>, Object> pred_assign = ts._state.get(theName);
						if(dice < theProb){
							pred_assign.put(thePars, (Object)true);
						}
						else{
							pred_assign.put(thePars, (Object)false);
						}
					}
				}
				
				//get the concrete action based on ts
				RandomConcurrentPolicyIndex randomGen = new RandomConcurrentPolicyIndex(ts);
				ArrayList<PVAR_INST_DEF> trialAction = randomGen.getCAction(ts);
				ts.computeNextState(trialAction, r);
				reward += ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
						cs, r)).doubleValue();
				
				
				for(PVAR_NAME pn: _alStateNames){
					ArrayList<ArrayList<LCONST>> terms = generateAtoms(pn);
					for(ArrayList<LCONST> t: terms){
						if(ts._nextState.containsKey(pn) && ts._nextState.get(pn).containsKey(t) &&
								(Boolean)(ts._nextState.get(pn).get(t))){
							if(!_nextState.containsKey(pn)){
								_nextState.put(pn, new HashMap<ArrayList<LCONST>, Double>());
							}
							else{
								if(!_nextState.get(pn).containsKey(t)){
								_nextState.get(pn).put(t, 1.0);
								}
								else{
									_nextState.get(pn).put(t, _nextState.get(pn).get(t).doubleValue() + 1.0);
								}
							}
						}
					}
				}	
			}
			for(PVAR_NAME pn: _alStateNames){
				ArrayList<ArrayList<LCONST>> terms = generateAtoms(pn);
				for(ArrayList<LCONST> t: terms){
					if(_nextState.containsKey(pn) && _nextState.get(pn).containsKey(t))
					_nextState.get(pn).put(t, _nextState.get(pn).get(t)/k);
				}
			}
			return reward / k;
		}
	}
	
	public void computeNextState(Random r) 
			throws EvalException {

			// Clear then set the actions
			for (PVAR_NAME p : _actions.keySet())
				_actions.get(p).clear();
			//setActions(actions);
			
			//System.out.println("Starting state: " + _state + "\n");
			//System.out.println("Starting nonfluents: " + _nonfluents + "\n");
			
			// First compute intermediate variables, level-by-level
			
			//***this part has not been dealt 
			//***no interm vars are supported in this version
			HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
			if (DISPLAY_UPDATES) System.out.println("Updating intermediate variables");
			for (Map.Entry<Pair, PVAR_NAME> e : _tmIntermNames.entrySet()) {
				int level   = (Integer)e.getKey()._o1;
				PVAR_NAME p = e.getValue();
				
				// Generate updates for each ground fluent
				//System.out.println("Updating interm var " + p + " @ level " + level + ":");
				ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
				
				for (ArrayList<LCONST> gfluent : gfluents) {
					if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent + " @ " + level + " := ");
					CPF_DEF cpf = _hmCPFs.get(p);
					
					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST)gfluent.get(i);
						subs.put(v,c);
					}
					
					Object value = cpf._exprEquals.sample(subs, this, r);
					if (DISPLAY_UPDATES) System.out.println(value);
					
					// Update value
					HashMap<ArrayList<LCONST>,Object> pred_assign = _interm.get(p);
					pred_assign.put(gfluent, value);
				}
			}
			
			// Do same for next-state (keeping in mind primed variables)
			//***first set from default value of state vars
			for (PVAR_NAME p : _alStateNames) {
				
				// Get default value
				Object def_value = null;
				PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
				def_value = ((PVARIABLE_STATE_DEF)pvar_def)._oDefValue;
				HashMap<ArrayList<LCONST>, Double> pred_assign = _nextState.get(p);
				double defaultDValue;
				if((Boolean)def_value){
					defaultDValue = 1.0;
				}
				else{
					defaultDValue = 0.0;
				}
				ArrayList<ArrayList<LCONST>> terms = generateAtoms(p);
				for(ArrayList<LCONST> term : terms){
					pred_assign.put(term, defaultDValue);
				}
			}
			
			//***then compute next state vars according to transition
			if (DISPLAY_UPDATES) System.out.println("Updating next state");
			for (PVAR_NAME p : _alStateNames) {
							
				// Get default value
				PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
				if (!(pvar_def instanceof PVARIABLE_STATE_DEF) ||
					((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
					throw new EvalException("Expected state variable, got nonfluent: " + p);
				
				// Generate updates for each ground fluent
				PVAR_NAME primed = new PVAR_NAME(p._sPVarName + "'");
				//System.out.println("Updating next state var " + primed + " (" + p + ")");
				ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
				
				for (ArrayList<LCONST> gfluent : gfluents) {
					if (DISPLAY_UPDATES) System.out.print("- " + primed + gfluent + " := ");
					CPF_DEF cpf = _hmCPFs.get(primed);
					
					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST)gfluent.get(i);
						subs.put(v,c);
					}
					
					Object v = cpf._exprEquals.sample(subs, this, r);
					if(!(v instanceof Double) && !(v instanceof Integer) && !(v instanceof Boolean) ){
						throw new EvalException("State: State vars can only be bool/int/double");
					}
					double value = getDouble(v);
					if (DISPLAY_UPDATES) System.out.println(value);
					
					// Update value if not default
					HashMap<ArrayList<LCONST>, Double> pred_assign = _nextState.get(p);
					pred_assign.put(gfluent, value);
				}
			}
			
			// Make sure observations are cleared prior to computing new ones
			for (PVAR_NAME p : _observ.keySet())
				_observ.get(p).clear();

			// Do same for observations... note that this occurs after the next state
			// update because observations in a POMDP may be modeled on the current
			// and next state, i.e., P(o|s,a,s').
			if (DISPLAY_UPDATES) System.out.println("Updating observations");
			for (PVAR_NAME p : _alObservNames) {
				
				// Generate updates for each ground fluent
				//System.out.println("Updating observation var " + p);
				ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
				
				for (ArrayList<LCONST> gfluent : gfluents) {
					if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent + " := ");
					CPF_DEF cpf = _hmCPFs.get(p);
					
					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST)gfluent.get(i);
						subs.put(v,c);
					}
					
					Object value = cpf._exprEquals.sample(subs, this, r);
					if (DISPLAY_UPDATES) System.out.println(value);
					
					// Update value
					HashMap<ArrayList<LCONST>,Object> pred_assign = _observ.get(p);
					pred_assign.put(gfluent, value);
				}
			}
		}
	
	
	public void computeNextState2(ArrayList<PVAR_INST_DEF> actions, Random r) 
		throws EvalException {

		// Clear then set the actions
		for (PVAR_NAME p : _actions.keySet())
			_actions.get(p).clear();
		setActions(actions);
		
		//System.out.println("Starting state: " + _state + "\n");
		//System.out.println("Starting nonfluents: " + _nonfluents + "\n");
		
		// First compute intermediate variables, level-by-level
		
		//***this part has not been dealt 
		//***no interm vars are supported in this version
		HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
		if (DISPLAY_UPDATES) System.out.println("Updating intermediate variables");
		for (Map.Entry<Pair, PVAR_NAME> e : _tmIntermNames.entrySet()) {
			int level   = (Integer)e.getKey()._o1;
			PVAR_NAME p = e.getValue();
			
			// Generate updates for each ground fluent
			//System.out.println("Updating interm var " + p + " @ level " + level + ":");
			ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
			
			for (ArrayList<LCONST> gfluent : gfluents) {
				if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent + " @ " + level + " := ");
				CPF_DEF cpf = _hmCPFs.get(p);
				
				subs.clear();
				for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
					LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
					LCONST c = (LCONST)gfluent.get(i);
					subs.put(v,c);
				}
				
				Object value = cpf._exprEquals.sample(subs, this, r);
				if (DISPLAY_UPDATES) System.out.println(value);
				
				// Update value
				HashMap<ArrayList<LCONST>,Object> pred_assign = _interm.get(p);
				pred_assign.put(gfluent, value);
			}
		}
		
		// Do same for next-state (keeping in mind primed variables)
		//***first set from default value of state vars
		for (PVAR_NAME p : _alStateNames) {
			
			// Get default value
			Object def_value = null;
			PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
			def_value = ((PVARIABLE_STATE_DEF)pvar_def)._oDefValue;
			HashMap<ArrayList<LCONST>, Double> pred_assign = _nextState.get(p);
			double defaultDValue;
			if((Boolean)def_value){
				defaultDValue = 1.0;
			}
			else{
				defaultDValue = 0.0;
			}
			ArrayList<ArrayList<LCONST>> terms = generateAtoms(p);
			for(ArrayList<LCONST> term : terms){
				pred_assign.put(term, defaultDValue);
			}
		}
		
		//***then compute next state vars according to transition
		if (DISPLAY_UPDATES) System.out.println("Updating next state");
		for (PVAR_NAME p : _alStateNames) {
						
			// Get default value
			PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
			if (!(pvar_def instanceof PVARIABLE_STATE_DEF) ||
				((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
				throw new EvalException("Expected state variable, got nonfluent: " + p);
			
			// Generate updates for each ground fluent
			PVAR_NAME primed = new PVAR_NAME(p._sPVarName + "'");
			//System.out.println("Updating next state var " + primed + " (" + p + ")");
			ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
			
			for (ArrayList<LCONST> gfluent : gfluents) {
				if (DISPLAY_UPDATES) System.out.print("- " + primed + gfluent + " := ");
				CPF_DEF cpf = _hmCPFs.get(primed);
				
				subs.clear();
				for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
					LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
					LCONST c = (LCONST)gfluent.get(i);
					subs.put(v,c);
				}
				
				Object v = cpf._exprEquals.sample(subs, this, r);
				if(!(v instanceof Double) && !(v instanceof Integer) && !(v instanceof Boolean) ){
					throw new EvalException("State: State vars can only be bool/int/double");
				}
				double value = getDouble(v);
				if (DISPLAY_UPDATES) System.out.println(value);
				
				// Update value if not default
				HashMap<ArrayList<LCONST>, Double> pred_assign = _nextState.get(p);
				pred_assign.put(gfluent, value);
			}
		}
		
		// Make sure observations are cleared prior to computing new ones
		for (PVAR_NAME p : _observ.keySet())
			_observ.get(p).clear();

		// Do same for observations... note that this occurs after the next state
		// update because observations in a POMDP may be modeled on the current
		// and next state, i.e., P(o|s,a,s').
		if (DISPLAY_UPDATES) System.out.println("Updating observations");
		for (PVAR_NAME p : _alObservNames) {
			
			// Generate updates for each ground fluent
			//System.out.println("Updating observation var " + p);
			ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
			
			for (ArrayList<LCONST> gfluent : gfluents) {
				if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent + " := ");
				CPF_DEF cpf = _hmCPFs.get(p);
				
				subs.clear();
				for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
					LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
					LCONST c = (LCONST)gfluent.get(i);
					subs.put(v,c);
				}
				
				Object value = cpf._exprEquals.sample(subs, this, r);
				if (DISPLAY_UPDATES) System.out.println(value);
				
				// Update value
				HashMap<ArrayList<LCONST>,Object> pred_assign = _observ.get(p);
				pred_assign.put(gfluent, value);
			}
		}
		//System.out.println("Inside: " + _nextState);
	}
	
	public void computeNextState(ArrayList<PVAR_INST_DEF> actions, Random r)
		throws EvalException{

			// Clear then set the actions
			for (PVAR_NAME p : _actions.keySet())
				_actions.get(p).clear();
			setPVariables(_actions, actions);
			
			//System.out.println("Starting state: " + _state + "\n");
			//System.out.println("Starting nonfluents: " + _nonfluents + "\n");
			
			// First compute intermediate variables, level-by-level
			HashMap<LVAR,LCONST> subs = new HashMap<LVAR,LCONST>();
			if (DISPLAY_UPDATES) System.out.println("Updating intermediate variables");
			for (Map.Entry<Pair, PVAR_NAME> e : _tmIntermNames.entrySet()) {
				int level   = (Integer)e.getKey()._o1;
				PVAR_NAME p = e.getValue();
				
				// Generate updates for each ground fluent
				//System.out.println("Updating interm var " + p + " @ level " + level + ":");
				ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
				
				for (ArrayList<LCONST> gfluent : gfluents) {
					if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent + " @ " + level + " := ");
					CPF_DEF cpf = _hmCPFs.get(p);
					
					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST)gfluent.get(i);
						subs.put(v,c);
					}
					
					Object value = cpf._exprEquals.sample(subs, this, r);
					if (DISPLAY_UPDATES) System.out.println(value);
					
					// Update value
					HashMap<ArrayList<LCONST>,Object> pred_assign = _interm.get(p);
					pred_assign.put(gfluent, value);
				}
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
					
					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST)gfluent.get(i);
						subs.put(v,c);
					}
					
					Object value = cpf._exprEquals.sample(subs, this, r);
					if (DISPLAY_UPDATES) System.out.println(value);
					
					// Update value if not default
					if (!value.equals(def_value)) {
						HashMap<ArrayList<LCONST>,Double> pred_assign = _nextState.get(p);
						pred_assign.put(gfluent, getDouble(value));
					}
				}
			}
			
			// Make sure observations are cleared prior to computing new ones
			for (PVAR_NAME p : _observ.keySet())
				_observ.get(p).clear();

			// Do same for observations... note that this occurs after the next state
			// update because observations in a POMDP may be modeled on the current
			// and next state, i.e., P(o|s,a,s').
			if (DISPLAY_UPDATES) System.out.println("Updating observations");
			for (PVAR_NAME p : _alObservNames) {
				
				// Generate updates for each ground fluent
				//System.out.println("Updating observation var " + p);
				ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);
				
				for (ArrayList<LCONST> gfluent : gfluents) {
					if (DISPLAY_UPDATES) System.out.print("- " + p + gfluent + " := ");
					CPF_DEF cpf = _hmCPFs.get(p);
					
					subs.clear();
					for (int i = 0; i < cpf._exprVarName._alTerms.size(); i++) {
						LVAR v = (LVAR)cpf._exprVarName._alTerms.get(i);
						LCONST c = (LCONST)gfluent.get(i);
						subs.put(v,c);
					}
					
					Object value = cpf._exprEquals.sample(subs, this, r);
					if (DISPLAY_UPDATES) System.out.println(value);
					
					// Update value
					HashMap<ArrayList<LCONST>,Object> pred_assign = _observ.get(p);
					pred_assign.put(gfluent, value);
				}
			}
		
	}
	public void advanceNextState() throws EvalException {
		// For backward compatibility with code that has previously called this
		// method with 0 parameters, we'll assume observations are cleared by default
		advanceNextState(true /* clear observations */);
	}
	
	public void advanceNextState(boolean clear_observations) throws EvalException {
		HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> temp = _state;
		_state = _nextState;
		_nextState = temp;
		
		// Clear the non-state, non-constant, non-action variables
		for (PVAR_NAME p : _nextState.keySet())
			_nextState.get(p).clear();
		for (PVAR_NAME p : _interm.keySet())
			_interm.get(p).clear();
		if (clear_observations)  
			for (PVAR_NAME p : _observ.keySet())
				_observ.get(p).clear();
	}
	
	public void clearPVariables(HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Object>> assign) {
		for (HashMap<ArrayList<LCONST>,Object> pred_assign : assign.values())
			pred_assign.clear();
	}
	
	public int setPVariables(HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> assign, 
							  ArrayList<PVAR_INST_DEF> src) throws EvalException {

		int non_def = 0;
		boolean fatal_error = false;
		for (PVAR_INST_DEF def : src) {
			
			// Get the assignments for this PVAR
			HashMap<ArrayList<LCONST>,Double> pred_assign = assign.get(def._sPredName);
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
				pred_assign.put(def._alTerms, getDouble(def._oValue));
				++non_def;
			} else if ( pvar_def instanceof PVARIABLE_OBS_DEF ) {
				pred_assign.put(def._alTerms, getDouble(def._oValue));
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
	
	public Object getPVariableAssign(PVAR_NAME p, ArrayList<LCONST> terms) {

		// Get default value if it exists
		Object def_value = null;
		boolean primed = p._bPrimed;
		p = new PVAR_NAME(p._sPVarName);
		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);

		if (pvar_def == null) {
			System.out.println("ERROR: undefined pvariable: " + p);
			return null;
		} else if (pvar_def._alParamTypes.size() != terms.size()) {
			System.out.println("ERROR: expected "
					+ pvar_def._alParamTypes.size() + " for " + p + ", got "
					+ terms.size());
			return null;
		}

		if (pvar_def instanceof PVARIABLE_STATE_DEF) // state & non_fluents
			def_value = ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;
		else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) // actions
			def_value = ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;

		// Get correct variable assignments
		HashMap<ArrayList<LCONST>, Double> var_src_d = null;
		HashMap<ArrayList<LCONST>, Object> var_src = null;
		int type = -1;
		if (pvar_def instanceof PVARIABLE_STATE_DEF
				&& ((PVARIABLE_STATE_DEF) pvar_def)._bNonFluent){
			type = 0;
			var_src_d = _nonfluents.get(p);
		}
		else if (pvar_def instanceof PVARIABLE_STATE_DEF
				&& !((PVARIABLE_STATE_DEF) pvar_def)._bNonFluent){
			type = 0;
			var_src_d = primed ? _nextState.get(p) : _state.get(p); 
		}
		else if (pvar_def instanceof PVARIABLE_ACTION_DEF){
			type = 0;
			var_src_d = _actions.get(p);
		}
		else if (pvar_def instanceof PVARIABLE_INTERM_DEF){
			type = 1;
			var_src = _interm.get(p);
		}
		else if (pvar_def instanceof PVARIABLE_OBS_DEF){
			type = 1;
			var_src = _observ.get(p);
		}
		if( type == 1 ){
			if (var_src == null) {
				System.out.println("ERROR: no variable source for " + p);
				return null;
			}
			
			// Lookup value, return default (if available) if value not found
			Object ret = var_src.get(terms);
			if (ret == null)
				ret = def_value;
			return ret;
		}
		else{
			if (var_src_d == null) {
				System.out.println("ERROR: no variable source for " + p);
				return null;
			}
			
			// Lookup value, return default (if available) if value not found
			Object ret = var_src_d.get(terms);
			if (ret == null)
				ret = def_value;
			return ret;
		}
	}
		
	public boolean setPVariableAssign(PVAR_NAME p, ArrayList<LCONST> terms, 
			Object value) throws EvalException {
		
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
					" for " + p + ", got " + terms.size());
			return false;
		}
		
		if (pvar_def instanceof PVARIABLE_STATE_DEF) // state & non_fluents
			def_value = ((PVARIABLE_STATE_DEF) pvar_def)._oDefValue;
		else if (pvar_def instanceof RDDL.PVARIABLE_ACTION_DEF) // actions
			def_value = ((PVARIABLE_ACTION_DEF) pvar_def)._oDefValue;

		// Get correct variable assignments
		HashMap<ArrayList<LCONST>,Object> var_src = null;
		HashMap<ArrayList<LCONST>,Double> var_src_stat = null;
		if (pvar_def instanceof PVARIABLE_STATE_DEF && ((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = _nonfluents.get(p);
		else if (pvar_def instanceof PVARIABLE_STATE_DEF && !((PVARIABLE_STATE_DEF)pvar_def)._bNonFluent)
			var_src_stat = primed ? _nextState.get(p) : _state.get(p);
		else if (pvar_def instanceof PVARIABLE_ACTION_DEF)
			var_src_stat = _actions.get(p);
		else if (pvar_def instanceof PVARIABLE_INTERM_DEF)
			var_src = _interm.get(p);
		else if (pvar_def instanceof PVARIABLE_OBS_DEF)
			var_src = _observ.get(p);
		
		if (var_src == null) {
			if(var_src_stat == null){
				System.out.println("ERROR: no variable source for " + p);
				return false;
			}
			else{
				var_src_stat.put(terms, getDouble(value));
				return true;
			}
		}

		// Set value (or remove if default)... n.b., def_value could be null if not s,a,s'
		if (value == null || value.equals(def_value)) {
			var_src.remove(terms);			
		} else {
			var_src.put(terms, value);
		}
		return true;
	}
			
	//////////////////////////////////////////////////////////////////////
	
	public ArrayList<ArrayList<LCONST>> generateAtoms(PVAR_NAME p) throws EvalException {
		ArrayList<ArrayList<LCONST>> list = new ArrayList<ArrayList<LCONST>>();
		PVARIABLE_DEF pvar_def = _hmPVariables.get(p);
		//System.out.print("Generating pvars for " + pvar_def + ": ");
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
			int a = 0;
			if(type._STypeName == "xgrid")
				{
					a = 1;
				}
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
					ArrayList<ArrayList<LCONST>> gfluents = generateAtoms(p);										
					for (ArrayList<LCONST> gfluent : gfluents)
						sb.append("- " + e.getKey() + ": " + p + 
								(gfluent.size() > 0 ? gfluent : "") + " := " + 
								getPVariableAssign(p, gfluent) + "\n");
						
				} catch (EvalException ex) {
					sb.append("- could not retrieve assignment" + e.getKey() + " for " + p + "\n");
				}
		}
				
		return sb.toString();
	}
}
