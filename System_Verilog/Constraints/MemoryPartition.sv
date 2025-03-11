// Memory Block Randomization
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// Start address of RAM
  bit [31:0] 		m_ram_end; 				// End address of RAM

  rand bit [31:0] 	m_start_addr; 			// Pointer to start address of block
  rand bit [31:0]   m_end_addr; 			// Pointer to last addr of block
  rand int 			m_block_size; 			// Block size in KB

  constraint c_addr { m_start_addr >= m_ram_start; 	// Block addr should be more than RAM start
                      m_start_addr < m_ram_end; 	// Block addr should be less than RAM end
                      m_start_addr % 4 == 0;  		// Block addr should be aligned to 4-byte boundary  4K-align
                      m_end_addr == m_start_addr + m_block_size - 1; };

  constraint c_blk_size { m_block_size inside {64, 128, 512}; }; 	// Block's size should be either 64/128/512 bytes

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
	$display ("Block StartAddr = 0x%0h", m_start_addr);
    $display ("Block EndAddr   = 0x%0h", m_end_addr);
    $display ("Block Size      = %0d bytes", m_block_size);
  endfunction
endclass

module tb;
  initial begin
    MemoryBlock mb = new;
    mb.m_ram_start = 32'h0;
    mb.m_ram_end   = 32'h7FF; 		// 2KB RAM
    mb.randomize();
    mb.display();
  end
endmodule

/*
    RAM StartAddr   = 0x0
    RAM EndAddr     = 0x7ff
    Block StartAddr = 0x714
    Block EndAddr   = 0x753
    Block Size      = 64 bytes
*/


// Equal partition
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// Start address of RAM
  bit [31:0] 		m_ram_end; 				// End address of RAM

  rand int			m_num_part; 			// Number of partitions
  rand bit [31:0] 	m_part_start []; 		// Partition start array
  rand int 			m_part_size; 		 	// Size of each partition
  rand int			m_tmp;

  // Constrain number of partitions RAM has to be divided into
  constraint c_parts { m_num_part > 4; m_num_part < 10; }       // 最多切 9 塊, 最少切 5 塊

  // Constraint size of each partition
  constraint c_size { m_part_size == (m_ram_end - m_ram_start)/m_num_part; }        // 平均切

  // Constrain start addr of each partition
  constraint c_part { m_part_start.size() == m_num_part;
                      foreach (m_part_start[i]) {
                        if (i)
                          m_part_start[i] == m_part_start[i-1] + m_part_size;
                        else
                          m_part_start[i] == m_ram_start;
                      }
                    }

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
    $display ("# Partitions = %0d", m_num_part);
    $display ("Partition Size = %0d bytes", m_part_size);
    $display ("------ Partitions --------");
    foreach (m_part_start[i])                   // 印出每個 partition 的 start addr
      $display ("Partition %0d start = 0x%0h", i, m_part_start[i]);
  endfunction
endclass

module tb;
  initial begin
    MemoryBlock mb = new;
    mb.m_ram_start = 32'h0;
    mb.m_ram_end   = 32'h7FF; 		// 2KB RAM
    mb.randomize();
    mb.display();
  end
endmodule

/*
    ------ Memory Block --------
    RAM StartAddr   = 0x0
    RAM EndAddr     = 0x7ff
    # Partitions = 9
    Partition Size = 227 bytes
    ------ Partitions --------
    Partition 0 start = 0x0
    Partition 1 start = 0xe3
    Partition 2 start = 0x1c6
    Partition 3 start = 0x2a9
    Partition 4 start = 0x38c
    Partition 5 start = 0x46f
    Partition 6 start = 0x552
    Partition 7 start = 0x635
    Partition 8 start = 0x718
*/


// Variable Memory Partition
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// Start address of RAM
  bit [31:0] 		m_ram_end; 				// End address of RAM

  rand int			m_num_part; 			// Number of partitions
  rand bit [31:0] 	m_part_start []; 		// Partition start array
  rand int 			m_part_size [];		 	// Size of each partition
  rand int			m_tmp;

  // Constrain number of partitions RAM has to be divided into
  constraint c_parts { m_num_part > 4; m_num_part < 10; }

  // Constraint size of each partition
  constraint c_size { 
                        m_part_size.size() == m_num_part;
                        m_part_size.sum() == m_ram_end - m_ram_start + 1;       // 這邊限制每個 partition 加總起來的 size 為多少
                        foreach (m_part_size[i])
                            m_part_size[i] inside {16, 32, 64, 128, 512, 1024}; // 這邊決定每個 partition 的 size
                    }

  // Constrain start addr of each partition
  constraint c_part { 
                        m_part_start.size() == m_num_part;
                        foreach (m_part_start[i]) {
                            if (i)
                            m_part_start[i] == m_part_start[i-1] + m_part_size[i-1];
                            else
                            m_part_start[i] == m_ram_start;
                      }
                    }

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
    $display ("# Partitions = %0d", m_num_part);
    $display ("------ Partitions --------");
    foreach (m_part_start[i])
      $display ("Partition %0d start = 0x%0h, size = %0d bytes", i, m_part_start[i], m_part_size[i]);
  endfunction
endclass

module tb;
  initial begin
    MemoryBlock mb = new;
    mb.m_ram_start = 32'h0;
    mb.m_ram_end   = 32'h7FF; 		// 2KB RAM
    mb.randomize();
    mb.display();
  end
endmodule

/*
    ------ Memory Block --------
    RAM StartAddr   = 0x0
    RAM EndAddr     = 0x7ff
    # Partitions = 7
    ------ Partitions --------
    Partition 0 start = 0x0, size = 512 bytes
    Partition 1 start = 0x200, size = 128 bytes
    Partition 2 start = 0x280, size = 64 bytes
    Partition 3 start = 0x2c0, size = 1024 bytes
    Partition 4 start = 0x6c0, size = 128 bytes
    Partition 5 start = 0x740, size = 128 bytes
    Partition 6 start = 0x7c0, size = 64 bytes
*/

// Variable Memory Partition with space in between
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// Start address of RAM
  bit [31:0] 		m_ram_end; 				// End address of RAM

  rand int			m_num_part; 			// Number of partitions
  rand bit [31:0] 	m_part_start []; 		// Partition start array
  rand int 			m_part_size [];		 	// Size of each partition
  rand int 			m_space[]; 	 			// Space between each partition     多一個 array 去紀錄每個 space partition 的 size
  rand int			m_tmp;

  // Constrain number of partitions RAM has to be divided into
  constraint c_parts { m_num_part > 4; m_num_part < 10; }

  // Constraint size of each partition
  constraint c_size { m_part_size.size() == m_num_part;
                     m_space.size() == m_num_part - 1;
                     m_space.sum() + m_part_size.sum() == m_ram_end - m_ram_start + 1;  // space + mem 總共 size 限制
                     foreach (m_part_size[i]) {
                       m_part_size[i] inside {16, 32, 64, 128, 512, 1024};      // 隨機產生 mem 和 space 的 size
                       if (i < m_space.size())              // for 最後一個 mem partition, space partition 不用再產生 size
                       	 m_space[i] inside {0, 16, 32, 64, 128, 512, 1024};
                     }
                    }

  // Constrain start addr of each partition
  constraint c_part { m_part_start.size() == m_num_part;
                      foreach (m_part_start[i]) {
                        if (i)
                          m_part_start[i] == m_part_start[i-1] + m_part_size[i-1] +  m_space[i-1];
                        else
                          m_part_start[i] == m_ram_start;
                      }
                    }

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
    $display ("# Partitions = %0d", m_num_part);
    $display ("------ Partitions --------");
    foreach (m_part_start[i])
      $display ("Partition %0d start = 0x%0h, size = %0d bytes, space = %0d bytes", i, m_part_start[i], m_part_size[i], m_space[i]);
  endfunction
endclass

module tb;
  initial begin
    MemoryBlock mb = new;
    mb.m_ram_start = 32'h0;
    mb.m_ram_end   = 32'h7FF; 		// 2KB RAM
    mb.randomize();
    mb.display();
  end
endmodule

/*
    ------ Memory Block --------
    RAM StartAddr   = 0x0
    RAM EndAddr     = 0x7ff
    # Partitions = 5
    ------ Partitions --------
    Partition 0 start = 0x0, size = 128 bytes, space = 64 bytes
    Partition 1 start = 0xc0, size = 32 bytes, space = 128 bytes
    Partition 2 start = 0x160, size = 32 bytes, space = 0 bytes
    Partition 3 start = 0x180, size = 1024 bytes, space = 512 bytes
    Partition 4 start = 0x780, size = 128 bytes, space = 0 bytes
*/


//* Partition for Programs and  Data
/*
    Memory is partitioned into regions for program, data and empty spaces. 
    A "dynamic array" is used to store the size for each program, data and empty space. 
    Using SystemVerilog constraints, the total size of all regions is matched with the total RAM space.

    The code shown below randomizes the total number of programs, data, and space regions. 
    This number also influences the size of each program, data and space so that the sum of all programs,
    data and empty spaces should be equal to the total RAM space.
 */
typedef struct {
  int start_addr;
  int end_addr;
} e_range;

class Space;
  rand int num_pgm;  		// Total number of programs required
  rand int num_data; 		// Total number of data blocks required
  rand int num_space; 		// Total number of empty spaces required

  rand int max_pgm_size; 	// Maximum program size
  rand int max_data_size; 	// Maximum data size

  rand int num_max_pgm; 	// Maximum number of programs

  rand int pgm_size[]; 		// Size of each program region      // 這裡都用 dynamic array 去紀錄 size
  rand int data_size[]; 	// Size of each data region
  rand int space_size[]; 	// Size of each empty space region

  int total_ram; 			// Total RAM space

  // Constrain maximum individual program region size to be 512 bytes
  // data region size to be 128 bytes and maximum number of programs in
  // this memory region to be 100
  constraint c_num_size { 	max_pgm_size 	== 512;
                            max_data_size 	== 128;
                         	num_max_pgm 	== 100;
                         }

  // Constrain total number of programs, data and space regions
  constraint c_num { 	num_pgm inside {[1:num_max_pgm]};
                    	num_data inside {[1:50]};
                    	num_space inside {[1:50]};
                   }

  // Constrain the array for program, data and space to equal the number
  // decided by the above constraints.
  constraint c_size { 	pgm_size.size() 	== num_pgm;
                    	data_size.size() 	== num_data;
                     	space_size.size() 	== num_space;
                   }

  // Size of each program/data/space is stored into indices of the corresponding
  // arrays. So, total size of RAM should be the sum of all programs + data + space
  constraint c_ram { foreach (pgm_size[i]) {
//    					pgm_size[i] inside {4, 8, 32, 64, 128, 512};
    					pgm_size[i] dist {[128:512]:/75, [32:64]:/20, [4:8]:/10};
    					pgm_size[i] % 4 == 0;
  					}
    				foreach (data_size[i]) {
                    	data_size[i] inside {64, 128, 512, 1024};
  					}
                      foreach (space_size[i]) {
                        space_size[i] inside {4, 8, 32, 64, 128, 512, 1024};
  					}
                      total_ram == pgm_size.sum() + data_size.sum() + space_size.sum();
                   }

  	// Function to display the partitioning
	function void display();
		$display("#pgms=%0d #data=%0d, #space=%0d", num_pgm, num_data, num_space);
		$display("#pgms.size=%0d #data.size=%0d, #space.size=%0d total=%0d", pgm_size.sum(), data_size.sum(), space_size.sum(), total_ram);
		foreach(pgm_size[i])
        	$display("pgm#%0d size=%0d bytes", i, pgm_size[i]);
		foreach(data_size[i])
            $display("data#%0d size=%0d bytes", i, data_size[i]);
		foreach(space_size[i])
        	$display("space#%0d size=%0d bytes", i, space_size[i]);
    endfunction
endclass

module tb;
  initial begin
    Space sp = new();
    sp.total_ram = 6 * 1024; 	// Assuem total 6KB memory space
    assert(sp.randomize());
    sp.display();
  end
endmodule



/*
    #pgms=37 #data=18, #space=47
    #pgms.size=3792 #data.size=1216, #space.size=1136 total=6144
    pgm#0 size=4 bytes
    pgm#1 size=200 bytes
    pgm#2 size=384 bytes
    pgm#3 size=4 bytes
    pgm#4 size=60 bytes
    pgm#5 size=44 bytes
    pgm#6 size=4 bytes
    pgm#7 size=4 bytes
    pgm#8 size=396 bytes
    pgm#9 size=164 bytes
    pgm#10 size=40 bytes
    pgm#11 size=188 bytes
    pgm#12 size=148 bytes
    pgm#13 size=152 bytes
    pgm#14 size=4 bytes
    pgm#15 size=48 bytes
    pgm#16 size=4 bytes
    pgm#17 size=32 bytes
    pgm#18 size=36 bytes
    pgm#19 size=180 bytes
    pgm#20 size=8 bytes
    pgm#21 size=4 bytes
    pgm#22 size=144 bytes
    pgm#23 size=48 bytes
    pgm#24 size=448 bytes
    pgm#25 size=4 bytes
    pgm#26 size=148 bytes
    pgm#27 size=4 bytes
    pgm#28 size=4 bytes
    pgm#29 size=4 bytes
    pgm#30 size=4 bytes
    pgm#31 size=4 bytes
    pgm#32 size=32 bytes
    pgm#33 size=4 bytes
    pgm#34 size=356 bytes
    pgm#35 size=476 bytes
    pgm#36 size=4 bytes
    data#0 size=64 bytes
    data#1 size=64 bytes
    data#2 size=64 bytes
    data#3 size=64 bytes
    data#4 size=64 bytes
    data#5 size=64 bytes
    data#6 size=64 bytes
    data#7 size=64 bytes
    data#8 size=64 bytes
    data#9 size=128 bytes
    data#10 size=64 bytes
    data#11 size=64 bytes
    data#12 size=64 bytes
    data#13 size=64 bytes
    data#14 size=64 bytes
    data#15 size=64 bytes
    data#16 size=64 bytes
    data#17 size=64 bytes
    space#0 size=4 bytes
    space#1 size=4 bytes
    space#2 size=4 bytes
    space#3 size=4 bytes
    space#4 size=4 bytes
    space#5 size=4 bytes
    space#6 size=4 bytes
    space#7 size=4 bytes
    space#8 size=128 bytes
    space#9 size=8 bytes
    space#10 size=4 bytes
    space#11 size=4 bytes
    space#12 size=4 bytes
    space#13 size=4 bytes
    space#14 size=32 bytes
    space#15 size=64 bytes
    space#16 size=512 bytes
    space#17 size=4 bytes
    space#18 size=32 bytes
    space#19 size=4 bytes
    space#20 size=4 bytes
    space#21 size=128 bytes
    space#22 size=4 bytes
    space#23 size=4 bytes
    space#24 size=4 bytes
    space#25 size=4 bytes
    space#26 size=8 bytes
    space#27 size=4 bytes
    space#28 size=4 bytes
    space#29 size=4 bytes
    space#30 size=4 bytes
    space#31 size=8 bytes
    space#32 size=4 bytes
    space#33 size=4 bytes
    space#34 size=4 bytes
    space#35 size=4 bytes
    space#36 size=64 bytes
    space#37 size=4 bytes
    space#38 size=4 bytes
    space#39 size=4 bytes
    space#40 size=4 bytes
    space#41 size=8 bytes
    space#42 size=4 bytes
    space#43 size=4 bytes
    space#44 size=4 bytes
    space#45 size=4 bytes
    space#46 size=4 bytes
*/