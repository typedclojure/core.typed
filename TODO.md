# TODO
* Handle the case for unique variables in loops.
    * Throw a type error if a unique variable occurs in a loop body.
    * No type error if it occurs as a loop binding.
* Handle the case for unique functions.
    * If a function closes over a unique variable, mark it as unique.
* Handle the case for unique variables in datatypes.
    * Unsure about all the details.
* Check the case for atoms.
