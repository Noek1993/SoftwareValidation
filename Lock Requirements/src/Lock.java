public class Lock {

	//@ invariant waterLevelLock > 0;
	//@ invariant waterLevelLock > 5;
	
	//@ invariant shipsInLock == 0 || shipsInLock == 1;
	
	float waterLevelLock;
	float waterLevelRight;
	float waterLevelLeft;
	boolean rightDoorOpen;
	boolean leftDoorOpen;
	int shipsWaitingRight;
	int shipsWaitingLeft;
	int shipsInLock;
	boolean shipBetweenDoors; // The ship being in an open door
	
	//@ requires waterLevelLock >= waterLevelLeft;
	//@ requires !rightDoorOpen;
	void OpenLeftDoor() {

	}

	//@ requires !shipBetweenDoors;
	void CloseLeftDoor() {

	}

	//@ requires waterLevelLock >= waterLevelRight;
	//@ requires !leftDoorOpen;
	void OpenRightDoor() {

	}

	//@ requires !shipBetweenDoors;
	void CloseRightDoor() {

	}

	//@ requires shipsInLock == 1;
	void RaiseWater() {

	}

	void LowerWater() {

	}

}