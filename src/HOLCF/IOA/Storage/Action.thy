(*  Title:      HOLCF/IOA/ABP/Action.thy
    ID:         $Id$
    Author:     Olaf M�ller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The set of all actions of the system.
*)

Action =  Main +
datatype action = New  | Loc nat | Free nat        
end
