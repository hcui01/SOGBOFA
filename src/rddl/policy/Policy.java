/**
 * RDDL: Implements abstract policy interface.
 * 
 * @author Scott Sanner (ssanner@gmail.com)
 * @version 10/10/10
 *
 **/

package rddl.policy;

import java.util.*;

import rddl.*;
import rddl.RDDL.*;
import rddl.competition.*;
public abstract class Policy {
	
	public Random _random = new Random();
	public long RAND_SEED = -1;	
	public String _sInstanceName;
	public RDDL rddl;
	public long _timeAllowed;
	public int symulationDepth = 3;
	public int currentRound = 0;
	public int NUM_CONCURRENT_ACTIONS;
	HashMap<TYPE_NAME,OBJECTS_DEF> _nonfluent_objects;
	 HashMap<TYPE_NAME,OBJECTS_DEF> _instance_objects;
	 HashMap<TYPE_NAME,TYPE_DEF> _typedefs;
	 HashMap<PVAR_NAME,PVARIABLE_DEF> _pvariables;
	 HashMap<PVAR_NAME,CPF_DEF> _cpfs;
	 ArrayList<PVAR_INST_DEF> _init_state;
	 ArrayList<PVAR_INST_DEF> _nonfluents;
	 ArrayList<BOOL_EXPR> _state_action_constraints;
	 EXPR _reward;
	 int _max_nondef_actions;
	 boolean ifPrint = false;
	 
	 DOMAIN _theDomain;
	 String _instanceName;
	 VisCounter _visCounter;
	

	public Policy() {
		symulationDepth = 5;
	}
	public Policy(String instance_name) {
		_sInstanceName = instance_name;
	}
	

	
	public void setCurrentRound(int round){
		currentRound = round;
	}
	
	public void setRandSeed(long rand_seed) {
		RAND_SEED = rand_seed;
		_random = new Random(RAND_SEED);
		
	}
	
	public void setRddlDomain(RDDL clientRddl){
		rddl = clientRddl;
	}
	
	public void setTimeAllowed(long time){
		_timeAllowed = time;
	}
	
	public void setVisCounter(VisCounter vis){
		_visCounter = vis;
	}
	
	public void setNumConcurrentActions(int num_concurrent) {
		NUM_CONCURRENT_ACTIONS = num_concurrent;
	}
	
	public void setDomain(DOMAIN theDoman){
		_theDomain = theDoman;
	}
	
	public void setInstanceName(String instance){
		_instanceName = instance;
	}
	
	public void setInitial(HashMap<TYPE_NAME,OBJECTS_DEF> nonfluent_objects,
			 HashMap<TYPE_NAME,OBJECTS_DEF> instance_objects,
			 HashMap<TYPE_NAME,TYPE_DEF> typedefs,
			 HashMap<PVAR_NAME,PVARIABLE_DEF> pvariables,
			 HashMap<PVAR_NAME,CPF_DEF> cpfs,
			 ArrayList<PVAR_INST_DEF> init_state,
			 ArrayList<PVAR_INST_DEF> nonfluents,
			 ArrayList<BOOL_EXPR> state_action_constraints,
			 EXPR reward, 
			 int max_nondef_actions,
			 DOMAIN theDomain,
			 String instanceName){
		_nonfluent_objects = nonfluent_objects;
		_instance_objects = instance_objects;
		_typedefs = typedefs;
		_pvariables = pvariables;
		_cpfs = cpfs;
		_init_state = init_state;
		_nonfluents = nonfluents;
		_state_action_constraints = state_action_constraints;
		_reward = reward;
		_max_nondef_actions = max_nondef_actions;
		_theDomain = theDomain;
		_instanceName = instanceName;
	}
	
	// Override if needed
	public void roundInit(double time_left, int horizon, int round_number, int total_rounds) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> ROUND INIT " + round_number + "/" + total_rounds + "; time remaining = " + time_left + ", horizon = " + horizon);
		System.out.println("*********************************************************");
	}
	
	
	
	// Override if needed
	public void roundEnd(double reward) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> ROUND END, reward = " + reward);
		System.out.println("*********************************************************");
	}
	
	// Override if needed
	public void sessionEnd(double total_reward) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> SESSION END, total reward = " + total_reward);
		System.out.println("*********************************************************");
	}

	// Must override
	public abstract ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException;
	
	
	public String toString() {
		return "Policy for '" + _sInstanceName + "'";
	}
}
