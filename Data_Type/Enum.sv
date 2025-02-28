/*
  enum          {RED, YELLOW, GREEN}         light_1;         // int type; RED = 0, YELLOW = 1, GREEN = 2
  enum bit[1:0] {RED, YELLOW, GREEN}         light_2;         // bit type; RED = 0, YELLOW = 1, GREEN = 2

  enum          {RED=3, YELLOW, GREEN}       light_3;         // RED = 3, YELLOW = 4, GREEN = 5
  enum          {RED = 4, YELLOW = 9, GREEN} light_4;         // RED = 4, YELLOW = 9, GREEN = 10 (automatically assigned)
  enum          {RED = 2, YELLOW, GREEN = 3} light_5;         // Error : YELLOW and GREEN are both assigned 3

  enum bit[0:0] {RED, YELLOW, GREEN} light_6;                 // Error: minimum 2 bits are required

  enum {1WAY, 2TIMES, SIXPACK=6} e_formula; 		// Compilation error on 1WAY, 2TIMES. Note that an enumeration name cannot start with a number !

  enum {ONEWAY, TIMES2, SIXPACK=6} e_formula; 	// Correct way is to keep the first character non-numeric
*/

module tb;
	// "e_true_false" is a new data-type with two valid values: TRUE and FALSE
	typedef enum {TRUE, FALSE} e_true_false;

	initial begin
		// Declare a variable of type "e_true_false" that can store TRUE or FALSE
		e_true_false  answer;

		// Assign TRUE/FALSE to the enumerated variable
		answer = TRUE;

		// Display string value of the variable
		// $display ("answer = %s", answer.name);
    $display ("answer = %0d", answer);
	end
endmodule

/*
  answer = 0
*/

/*
  answer = TRUE
*/