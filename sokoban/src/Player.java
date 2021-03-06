/**
 * Represents a player. Technically, a player could be a board item, but we keep 
 * her/him separate. 
 */
final class Player
{

  /** @informal a player always has a position */
  //@ public invariant position != null;
  public Position position;

  /** @informal based on valid parameters the constructor creates a valid player object */
  //@ assignable this.position;
  //@ ensures this.position.equals (position);
  Player (Position position) {
    this.position = position;
  }


  /** @informal a player can only change position to a valid new position */
  //@ assignable position;
  //@ requires position.isValidNextPosition (newPosition);
  //@ ensures this.position.equals (position);
  public void setPosition (Position newPosition) {
	    this.position = newPosition;
  }

  //@ skipesc
  public /*@ pure non_null @*/ String toString () {
    return "Player(" + position.x + "," + position.y + ")";
  }

}
