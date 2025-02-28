/*
	                Operator	                              Semantics
Equality	      Str1 == Str2	                Returns 1 if the two strings are equal and 0 if they are not
Inequality	    Str1 != Str2	                Returns 1 if the two strings are not equal and 0 if they are
Comparison	    Str1 < Str2
                Str1 <= Str2
                Str1 > Str2
                Str1 >= Str2	                Returns 1 if the correspondig condition is true and 0 if false
Concatenation	  {Str1, Str2, ..., StrN}	      All strings will be concatenated into one resultant string
Replication	    {multiplier{Str}}	            Replicates the string N number of times, where N is specified by the multiplier
Indexing	      Str[index]	                  Returns a byte, the ASCII code at the given index. If given index is out of range, it returns 0
Methods	        Str.method([args])	          The dot(.) operator is used to call string functions
*/
module tb;
  string firstname = "Joey";
  string lastname  = "Tribbiani";

  initial begin
    // String Equality : Check if firstname equals or not equals lastname
    if (firstname == lastname)
      $display ("firstname=%s is EQUAL to lastname=%s", firstname, lastname);

    if (firstname != lastname)
      $display ("firstname=%s is NOT EQUAL to lastname=%s", firstname, lastname); // V

    // String comparison : Check if length of firstname < length of lastname
    if (firstname < lastname)
      $display ("firstname=%s is LESS THAN lastname=%s", firstname, lastname);  // V

    // String comparison : Check if length of firstname > length of lastname
    if (firstname > lastname)
      $display ("firstname=%s is GREATER THAN lastname=%s", firstname, lastname);

    // String concatenation : Join first and last names into a single string
    $display ("Full Name = %s", {firstname, " ", lastname});  // V

    // String Replication
    $display ("%s", {3{firstname}});  // V

    // String Indexing : Get the ASCII character at index number 2 of both first and last names
    $display ("firstname[2]=%s lastname[2]=%s", firstname[2], lastname[2]); // V

  end
endmodule

/*
    firstname=Joey is NOT EQUAL to lastname=Tribbiani
    firstname=Joey is LESS THAN lastname=Tribbiani
    Full Name = Joey Tribbiani
    JoeyJoeyJoey
    firstname[2]=e lastname[2]=i
*/