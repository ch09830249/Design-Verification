// 和 C 一樣
module tb;
  initial begin
  	// 1. Declare an integer variable to hold the file descriptor
  	int fd;

  	// 2. Open a file called "note.txt" in the current folder with a "read" permission
  	// If the file does not exist, then fd will be zero
    fd = $fopen ("./note.txt", "r");
    if (fd)  $display("File was opened successfully : %0d", fd);
    else     $display("File was NOT opened successfully : %0d", fd);

    // 2. Open a file called "note.txt" in the current folder with a "write" permission
    //    "fd" now points to the same file, but in write mode
    fd = $fopen ("./note.txt", "w");
    if (fd)  $display("File was opened successfully : %0d", fd);
    else     $display("File was NOT opened successfully : %0d", fd);

    // 3. Close the file descriptor
    $fclose(fd);
  end
endmodule

/*
    Open failed on file "./note.txt". No such file or directory
    File was NOT opened successfully : 0
    File was opened successfully : -2147483645
*/


/*
 Argument	    Description
    "r"	        Open for reading
    "w"	        Create for writing, overwrite if it exists
    "a"	        Create if file does not exist, else append; open for writing at end of file
    "r+"	    Open for update (reading and writing)
    "w+"	    Truncate or create for update
    "a+"	    Append, open or create for update at EOF
*/
// 用不同 mode 開啟檔案
module tb;
  initial begin
  	int fd_w, fd_r, fd_a, fd_wp, fd_rp, fd_ap;

    fd_w = $fopen ("./todo.txt", "w"); 	// Open a new file in write mode and store file descriptor in fd_w
    fd_r = $fopen ("./todo.txt", "r"); 	// Open in read mode
    fd_a = $fopen ("./todo.txt", "a"); 	// Open in append mode


    if (fd_w)     $display("File was opened successfully : %0d", fd_w);
    else      	  $display("File was NOT opened successfully : %0d", fd_w);

    if (fd_r)     $display("File was opened successfully : %0d", fd_r);
    else      	  $display("File was NOT opened successfully : %0d", fd_r);

    if (fd_a)     $display("File was opened successfully : %0d", fd_a);
    else      	  $display("File was NOT opened successfully : %0d", fd_a);

    // Close the file descriptor
    $fclose(fd_w);
    $fclose(fd_r);
    $fclose(fd_a);
  end
endmodule
/*
    As you can see from the log shown below, 
    all three variables have a different value and each one points to the same file, 
    but with different access permissions.
*/
/*
    ncsim: *W,VFOPTW: File ./todo.txt being opened by Initial stmt (file: ./testbench.sv, line: 2 in worklib.tb [module]) has been opened earlier.
    File was opened successfully : -2147483645
    File was opened successfully : -2147483644
    File was opened successfully : -2147483643
*/

/*
    Files should be opened in the write w mode, or append a mode. 
    System tasks like "$fdisplay()" and "$fwrite()" can be used to write a formatted string into the file.
    The first argument of these tasks is the file descriptor handle and the second will be the data to be stored.
*/
/*
    To read a file, it has to be opened in either read r mode or read-write r+ mode. "$fgets()" is 
    a system task that will read a single line from the file.
*/

module tb;
  int 	 fd; 			// Variable for file descriptor handle
  string line; 			// String value read from the file

  initial begin

    // 1. Lets first open a new file and write some contents into it
    fd = $fopen ("trial", "w");

    // Write each index in the for loop to the file using $fdisplay
    // File handle should be the first argument
    for (int i = 0; i < 5; i++) begin
      $fdisplay (fd, "Iteration = %0d", i);         // 寫 5 行
    end

    // Close this file handle
    $fclose(fd);


    // 2. Let us now read back the data we wrote in the previous step
    fd = $fopen ("trial", "r");

    // Use $fgets to read a single line into variable "line"
    $fgets(line, fd);
    $display ("Line read : %s", line);

    // Get the next line and display
    $fgets(line, fd);
    $display ("Line read : %s", line);

    // Close this file handle
    $fclose(fd);
  end
endmodule

/*
    Line read : Iteration = 0       // 剛剛寫入的第一行

    Line read : Iteration = 1       // 剛剛寫入的第二行
*/


module tb;
  int 	 fd; 			// Variable for file descriptor handle
  string line; 			// String value read from the file

  initial begin
    // 1. Lets first open a new file and write some contents into it
    fd = $fopen ("trial", "w");
    for (int i = 0; i < 5; i++) begin
      $fdisplay (fd, "Iteration = %0d", i);
    end
    $fclose(fd);


    // 2. Let us now read back the data we wrote in the previous step
    fd = $fopen ("trial", "r");

    while (!$feof(fd)) begin            // 若還不是 end of file, 讀該行
      $fgets(line, fd);
      $display ("Line: %s", line);
    end

    // Close this file handle
    $fclose(fd);
  end
endmodule

/*
    Line: Iteration = 0

    Line: Iteration = 1

    Line: Iteration = 2

    Line: Iteration = 3

    Line: Iteration = 4

    Line: 
*/




module tb;
  int 	 fd; 			// Variable for file descriptor handle
  int 	 idx;
  string str;

  initial begin
    // 1. Lets first open a new file and write some contents into it
    fd = $fopen ("trial", "w");
    for (int i = 0; i < 5; i++)
      $fdisplay (fd, "Iteration = %0d", i);
    $fclose(fd);


    // 2. Let us now read back the data we wrote in the previous step
    fd = $fopen ("trial", "r");

    // fscanf returns the number of matches
    while ($fscanf (fd, "%s = %0d", str, idx) == 2) begin   // 就是 C 的 scanf, 從 file 讀後 parse 出 str 和 idx
      $display ("Line: %s = %0d", str, idx);    // parse 完, print it
    end

    // Close this file handle
    $fclose(fd);
  end
endmodule

/*
    Line: Iteration = 0
    Line: Iteration = 1
    Line: Iteration = 2
    Line: Iteration = 3
    Line: Iteration = 4
*/