/*
  Usage	                  Definition	                                  Comments
str.len()	            function int len()	                        Returns the number of characters in the string
str.putc()	          function void putc (int i, byte c);	        Replaces the ith character in the string with the given character
str.getc()	          function byte getc (int i);	                Returns the ASCII code of the ith character in str
str.tolower()	        function string tolower();	                Returns a string with characters in str converted to lowercase
str.compare(s)	      function int compare (string s);	          Compares str and s, as in the ANSI C strcmp function
str.icompare(s)	      function int icompare (string s);	          Compares str and s, like the ANSI C strcmp function
str.substr (i, j)	    function string substr (int i, int j);	    Returns a new string that is a substring formed by characters in position i through j of str
===Conversion===
str.atoi()	          function integer atoi();	                  Returns the integer corresponding to the ASCII decimal representation in str
str.atohex()	        function integer atohex();	                Interprets the string as hexadecimal
str.atooct()	        function integer atooct();	                Interprets the string as octal
str.atobin()	        function integer atobin();	                Interprets the string as binary
str.atoreal()	        function real atoreal();	                  Returns the real number corresponding to the ASCII decimal representation in str
str.itoa(i)	          function void itoa (integer i);	            Stores the ASCII decimal representation of i into str
str.hextoa(i)	        function void hextoa (integer i);	          Stores the ASCII hexadecimal representation of i into str
str.octtoa(i)	        function void octtoa (integer i);	          Stores the ASCII octal representation of i into str
str.bintoa(i)	        function void bintoa (integer i);	          Stores the ASCII binary representation of i into str
str.realtoa(r)	      function void realtoa (real r);	            Stores the ASCII real representation of r into str
*/

module tb;
   string str = "Hello World!";

   initial begin
   	  string tmp;

	  // Print length of string "str"
      $display ("str.len() = %0d", str.len());

      // Assign to tmp variable and put char "d" at index 3
      tmp = str;
      tmp.putc (3,"d");
      $display ("str.putc(3, d) = %s", tmp);

      // Get the character at index 2
      $display ("str.getc(2) = %s (%0d)", str.getc(2), str.getc(2));    //ASCII

      // Convert all characters to lower case
      $display ("str.tolower() = %s", str.tolower());

      // Comparison
      tmp = "Hello World!";
      $display ("[tmp,str are same] str.compare(tmp) = %0d", str.compare(tmp));
      tmp = "How are you ?";
      $display ("[tmp,str are diff] str.compare(tmp) = %0d", str.compare(tmp));

      // Ignore case comparison
      tmp = "hello world!";
      $display ("[tmp is in lowercase] str.compare(tmp) = %0d", str.compare(tmp));
      tmp = "Hello World!";
      $display ("[tmp,str are same] str.compare(tmp) = %0d", str.compare(tmp));

      // Extract new string from i to j
      $display ("str.substr(4,8) = %s", str.substr (4,8));

   end
endmodule

/*

*/

/*
    str.len() = 12                               
    str.putc(3, d) = Heldo World!
    str.getc(2) = l (108)
    str.tolower() = hello world!
    [tmp,str are same] str.compare(tmp) = 0
    [tmp,str are diff] str.compare(tmp) = -1
    [tmp is in lowercase] str.compare(tmp) = -1
    [tmp,str are same] str.compare(tmp) = 0
    str.substr(4,8) = o Wor
*/