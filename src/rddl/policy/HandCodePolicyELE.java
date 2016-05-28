package rddl.policy;

import java.util.ArrayList;
import java.util.Map;

import rddl.AState;
import rddl.EvalException;
import rddl.RDDL.TYPE_NAME;
import rddl.State;
import rddl.RDDL.LCONST;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class HandCodePolicyELE extends Policy {
	
	int MAX_FLOOR = -1;
	int NUMBER_ELE = -1;
	float PROB_DECLINE = 1.0f;
	
	boolean[] _waitingFloor;
	int[] _position;
	boolean[] _hasPeople;
	boolean[] _available;
	boolean[] _dirUp;
	
	public HandCodePolicyELE() { 
		super();
	}
	
	public HandCodePolicyELE(String instance_name) {
		super(instance_name);
	}
	@Override
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		
//		NUMBER_ELE = s._nonfluents.
		

		ArrayList<LCONST> objects = s._hmObject2Consts.get(new TYPE_NAME("floor"));
		MAX_FLOOR = objects.size();
		
		objects = s._hmObject2Consts.get(new TYPE_NAME("elevator"));
		NUMBER_ELE = objects.size();
		
		_waitingFloor = new boolean[MAX_FLOOR + 1];
		_position = new int[NUMBER_ELE + 1];
		_hasPeople = new boolean[NUMBER_ELE + 1];
		_available = new boolean[NUMBER_ELE + 1];
		_dirUp = new boolean[NUMBER_ELE + 1];
		
		for( int i = 0; i <= MAX_FLOOR; i ++){
			_waitingFloor[i] = false;
		}
		for( int i = 0; i <= NUMBER_ELE; i ++){
			_position[i] = 0;
		}
		for( int i = 0; i <= NUMBER_ELE; i ++){
			_hasPeople[i] = false;
			_available[i] = true;
			_dirUp[i] = false;
		}
		//store the state variables
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
		
		// Go through all variable types (state, interm, observ, action, nonfluent)
		for (Map.Entry<String,ArrayList<PVAR_NAME>> e : s._hmTypeMap.entrySet()) {
			
			if (!e.getKey().equals("states"))
				continue;
			
			// Go through all variable names p for a variable type
			for (PVAR_NAME p : e.getValue()){
				
				try {
					// Go through all term groundings for variable p
					ArrayList<ArrayList<LCONST>> gfluents = s.generateAtoms(p);										
					for (ArrayList<LCONST> gfluent : gfluents){
						if( s.getPVariableAssign(p, gfluent).toString().equals("true")){
							if(p._sPVarName.equals("person-waiting-up")){
								int rightPos = gfluent.toString().lastIndexOf("]");
								int theFloor = Integer.parseInt(gfluent.toString().substring(2, rightPos));
								_waitingFloor[theFloor] = true;
							}
							else{
								if( p._sPVarName.equals("elevator-at-floor")){
									int leftPos = 2;
									int rightPos = gfluent.toString().lastIndexOf(",");
									int theEle = Integer.parseInt(gfluent.toString().substring(leftPos, rightPos));
									leftPos = gfluent.toString().lastIndexOf("f") + 1;
									rightPos = gfluent.toString().lastIndexOf("]");
									int thePosition = Integer.parseInt(gfluent.toString().substring(leftPos, rightPos));
									_position[theEle] = thePosition;
								}
								else{
									if(p._sPVarName.equals("person-in-elevator-going-up")){
										int rightPos = gfluent.toString().lastIndexOf("]");
										int theEle = Integer.parseInt(gfluent.toString().substring(2,rightPos));
										_hasPeople[theEle] = true;
									}
									else{
										if(p._sPVarName.equals("elevator-dir-up")){
											int rightPos = gfluent.toString().lastIndexOf("]");
											int theEle = Integer.parseInt(gfluent.toString().substring(2,rightPos));
											_dirUp[theEle] = true;
										}
									}
								}
							}
						}
						else{
							continue;
						}
					}		
				} catch (EvalException ex) {
				}
			}
		}
		
		for(int i = 0; i <= MAX_FLOOR - 1; i ++){
			if( _waitingFloor[i] ){
				int _maxDistance = MAX_FLOOR + 1;
				int selectEle = -1;
				boolean[] selectable = new boolean[NUMBER_ELE];
				for(int j = 0; j <= NUMBER_ELE - 1; j ++){
					selectable[j] = true;
				}
				boolean ifRepeat = true;
				while( ifRepeat ){
					_maxDistance = MAX_FLOOR + 1;
					selectEle = -1;
					for(int j = 0; j <= NUMBER_ELE - 1; j ++){
						if( _available[j] && selectable[j] && Math.abs(i - _position[j]) < _maxDistance ){
							_maxDistance = Math.abs(i - _position[j]);
							selectEle = j;
						}
					}
					ifRepeat = false;
					//if the selected elevator has people waiting up, there is a chance that
					//decline the request and insist going up
					if( selectEle != -1 && _hasPeople[selectEle] && i < _position[selectEle]){
						int lotery = _random.nextInt(10) + 1;
						if((float)lotery / 10f <= PROB_DECLINE){
							selectable[selectEle] = false;
							ifRepeat = true;
						}
					}
				}
				if( selectEle == -1 ){
					continue;
				}
				String _actionValue;
				if( i == _position[selectEle] ){
					if( _dirUp[selectEle] ){
						continue;
					}
					else{
						_actionValue = "change-dir";
					}
				}
				else{
					if( i > _position[selectEle] ){
						_actionValue = "move-up";
					}
					else{
						_actionValue = "move-down";
					}
				}
				String a = String.valueOf(selectEle);
				boolean ifBreak = false;
				for(int j =0; j< s._alActionNames.size(); j++){
					
					// Get a random action
					PVAR_NAME p = s._alActionNames.get(j);
					if(!p.toString().equals(_actionValue)){
						continue;
					}
					// Get term instantations for that action and select *one*
					ArrayList<ArrayList<LCONST>> inst = s.generateAtoms(p);
					for (ArrayList<LCONST> terms : inst) {
						if(terms.toString().substring(1,3).equals("e" + a)){
							boolean value = true;
							actions.add(new PVAR_INST_DEF(p._sPVarName, value, terms));
							_available[selectEle] = false;
							ifBreak = true;
							break;
						}
					}
					if(ifBreak){
						break;
					}
				}
			}
		}
		
		for(int i = 0; i <= NUMBER_ELE - 1; i ++){
			if(_available[i] && _hasPeople[i]){
				String a = String.valueOf(i);
				boolean ifBreak = false;
				for(int j =0; j< s._alActionNames.size(); j++){
					
					// Get a random action
					PVAR_NAME p = s._alActionNames.get(j);
					if(!p.toString().equals("move-up")){
						continue;
					}
					// Get term instantations for that action and select *one*
					ArrayList<ArrayList<LCONST>> inst = s.generateAtoms(p);
					for (ArrayList<LCONST> terms : inst) {
						if(terms.toString().substring(1,3).equals("e" + a)){
							boolean value = true;
							actions.add(new PVAR_INST_DEF(p._sPVarName, value, terms));
							_available[i] = false;
							ifBreak = true;
							break;
						}
					}
					if(ifBreak){
						break;
					}
				}
			}
		}
		return actions;
	}

public ArrayList<PVAR_INST_DEF> getActions(AState s) throws EvalException {
		
//		NUMBER_ELE = s._nonfluents.
		

		ArrayList<LCONST> objects = s._hmObject2Consts.get(new TYPE_NAME("floor"));
		MAX_FLOOR = objects.size();
		
		objects = s._hmObject2Consts.get(new TYPE_NAME("elevator"));
		NUMBER_ELE = objects.size();
		
		_waitingFloor = new boolean[MAX_FLOOR + 1];
		_position = new int[NUMBER_ELE + 1];
		_hasPeople = new boolean[NUMBER_ELE + 1];
		_available = new boolean[NUMBER_ELE + 1];
		_dirUp = new boolean[NUMBER_ELE + 1];
		
		for( int i = 0; i <= MAX_FLOOR; i ++){
			_waitingFloor[i] = false;
		}
		for( int i = 0; i <= NUMBER_ELE; i ++){
			_position[i] = 0;
		}
		for( int i = 0; i <= NUMBER_ELE; i ++){
			_hasPeople[i] = false;
			_available[i] = true;
			_dirUp[i] = false;
		}
		//store the state variables
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
		
		// Go through all variable types (state, interm, observ, action, nonfluent)
		for (Map.Entry<String,ArrayList<PVAR_NAME>> e : s._hmTypeMap.entrySet()) {
			
			if (!e.getKey().equals("states"))
				continue;
			
			// Go through all variable names p for a variable type
			for (PVAR_NAME p : e.getValue()){
				
				try {
					// Go through all term groundings for variable p
					ArrayList<ArrayList<LCONST>> gfluents = s.generateAtoms(p);										
					for (ArrayList<LCONST> gfluent : gfluents){
						if( s.getDouble(s.getPVariableAssign(p, gfluent)) >= 0.5){
							if(p._sPVarName.equals("person-waiting-up")){
								int rightPos = gfluent.toString().lastIndexOf("]");
								int theFloor = Integer.parseInt(gfluent.toString().substring(2, rightPos));
								_waitingFloor[theFloor] = true;
							}
							else{
								if( p._sPVarName.equals("elevator-at-floor")){
									int leftPos = 2;
									int rightPos = gfluent.toString().lastIndexOf(",");
									int theEle = Integer.parseInt(gfluent.toString().substring(leftPos, rightPos));
									leftPos = gfluent.toString().lastIndexOf("f") + 1;
									rightPos = gfluent.toString().lastIndexOf("]");
									int thePosition = Integer.parseInt(gfluent.toString().substring(leftPos, rightPos));
									_position[theEle] = thePosition;
								}
								else{
									if(p._sPVarName.equals("person-in-elevator-going-up")){
										int rightPos = gfluent.toString().lastIndexOf("]");
										int theEle = Integer.parseInt(gfluent.toString().substring(2,rightPos));
										_hasPeople[theEle] = true;
									}
									else{
										if(p._sPVarName.equals("elevator-dir-up")){
											int rightPos = gfluent.toString().lastIndexOf("]");
											int theEle = Integer.parseInt(gfluent.toString().substring(2,rightPos));
											_dirUp[theEle] = true;
										}
									}
								}
							}
						}
						else{
							continue;
						}
					}		
				} catch (EvalException ex) {
				}
			}
		}
		
		for(int i = 0; i <= MAX_FLOOR - 1; i ++){
			if( _waitingFloor[i] ){
				int _maxDistance = MAX_FLOOR + 1;
				int selectEle = -1;
				boolean[] selectable = new boolean[NUMBER_ELE];
				for(int j = 0; j <= NUMBER_ELE - 1; j ++){
					selectable[j] = true;
				}
				boolean ifRepeat = true;
				while( ifRepeat ){
					_maxDistance = MAX_FLOOR + 1;
					selectEle = -1;
					for(int j = 0; j <= NUMBER_ELE - 1; j ++){
						if( _available[j] && selectable[j] && Math.abs(i - _position[j]) < _maxDistance ){
							_maxDistance = Math.abs(i - _position[j]);
							selectEle = j;
						}
					}
					ifRepeat = false;
					//if the selected elevator has people waiting up, there is a chance that
					//decline the request and insist going up
					if( selectEle != -1 && _hasPeople[selectEle] && i < _position[selectEle]){
						int lotery = _random.nextInt(10) + 1;
						if((float)lotery / 10f <= PROB_DECLINE){
							selectable[selectEle] = false;
							ifRepeat = true;
						}
					}
				}
				if( selectEle == -1 ){
					continue;
				}
				String _actionValue;
				if( i == _position[selectEle] ){
					if( _dirUp[selectEle] ){
						continue;
					}
					else{
						_actionValue = "change-dir";
					}
				}
				else{
					if( i > _position[selectEle] ){
						_actionValue = "move-up";
					}
					else{
						_actionValue = "move-down";
					}
				}
				String a = String.valueOf(selectEle);
				boolean ifBreak = false;
				for(int j =0; j< s._alActionNames.size(); j++){
					
					// Get a random action
					PVAR_NAME p = s._alActionNames.get(j);
					if(!p.toString().equals(_actionValue)){
						continue;
					}
					// Get term instantations for that action and select *one*
					ArrayList<ArrayList<LCONST>> inst = s.generateAtoms(p);
					for (ArrayList<LCONST> terms : inst) {
						if(terms.toString().substring(1,3).equals("e" + a)){
							boolean value = true;
							actions.add(new PVAR_INST_DEF(p._sPVarName, value, terms));
							_available[selectEle] = false;
							ifBreak = true;
							break;
						}
					}
					if(ifBreak){
						break;
					}
				}
			}
		}
		
		for(int i = 0; i <= NUMBER_ELE - 1; i ++){
			if(_available[i] && _hasPeople[i]){
				String a = String.valueOf(i);
				boolean ifBreak = false;
				for(int j =0; j< s._alActionNames.size(); j++){
					
					// Get a random action
					PVAR_NAME p = s._alActionNames.get(j);
					if(!p.toString().equals("move-up")){
						continue;
					}
					// Get term instantations for that action and select *one*
					ArrayList<ArrayList<LCONST>> inst = s.generateAtoms(p);
					for (ArrayList<LCONST> terms : inst) {
						if(terms.toString().substring(1,3).equals("e" + a)){
							boolean value = true;
							actions.add(new PVAR_INST_DEF(p._sPVarName, value, terms));
							_available[i] = false;
							ifBreak = true;
							break;
						}
					}
					if(ifBreak){
						break;
					}
				}
			}
		}
		return actions;
	}
}
