/*
  name	            The next number will be associated with name
  name = C	        Associates the constant C to name
  name[N]	          Generates N named constants : name0, name1, ..., nameN-1
  name[N] = C	      First named constant gets value C and subsequent ones are associated to consecutive values
  name[N:M]	        First named constant will be nameN and last named constant nameM, where N and M are integers
  name[N:M] = C	    First named constant, nameN will get C and subsequent ones are associated to consecutive values until nameM
*/

module tb;
  // name : The next number will be associated with name starting from 0
  // GREEN = 0, YELLOW = 1, RED = 2, BLUE = 3
  typedef enum {GREEN, YELLOW, RED, BLUE} color_set_1;

  // name = C : Associates the constant C to name
  // MAGENTA = 2, VIOLET = 7, PURPLE = 8, PINK = 9
  typedef enum {MAGENTA=2, VIOLET=7, PURPLE, PINK} color_set_2;

  // name[N] : Generates N named constants : name0, name1, ..., nameN-1
  // BLACK0 = 0, BLACK1 = 1, BLACK2 = 2, BLACK3 = 3
  typedef enum {BLACK[4]} color_set_3;

  // name[N] = C : First named constant gets value C and subsequent ones
  // are associated to consecutive values
  // RED0 = 5, RED1 = 6, RED2 = 7
  typedef enum {RED[3] = 5} color_set_4;

  // name[N:M] : First named constant will be nameN and last named
  // constant nameM, where N and M are integers
  // YELLOW3 = 0, YELLOW4 = 1, YELLOW5 = 2
  typedef enum {YELLOW[3:5]} color_set_5;

  // name[N:M] = C : First named constant, nameN will get C and
  // subsequent ones are associated to consecutive values until nameM
  // WHITE3 = 4, WHITE4 = 5, WHITE5 = 6
  typedef enum {WHITE[3:5] = 4} color_set_6;

  initial begin
    // Create new variables for each enumeration style
  	color_set_1 color1;
    color_set_2 color2;
    color_set_3 color3;
    color_set_4 color4;
    color_set_5 color5;
    color_set_6 color6;

    color1 = YELLOW; $display ("color1 = %0d, name = %s", color1, color1.name());
    color2 = PURPLE; $display ("color2 = %0d, name = %s", color2, color2.name());
    color3 = BLACK3; $display ("color3 = %0d, name = %s", color3, color3.name());
    color4 = RED1;   $display ("color4 = %0d, name = %s", color4, color4.name());
    color5 = YELLOW3;$display ("color5 = %0d, name = %s", color5, color5.name());
    color6 = WHITE4; $display ("color6 = %0d, name = %s", color6, color6.name());

  end
endmodule

/*
  color1 = 1, name = YELLOW
  color2 = 8, name = PURPLE
  color3 = 3, name = BLACK3
  color4 = 6, name = RED1
  color5 = 0, name = YELLOW3
  color6 = 5, name = WHITE4
*/