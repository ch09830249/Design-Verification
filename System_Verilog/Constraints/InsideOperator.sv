constraint my_range { typ > 32;
                      typ < 256; }

// typ >= 32 and typ <= 256
constraint new_range { typ inside {[32:256]}; }

// Choose from the following values
constraint spec_range { type inside {32, 64, 128}; }

/* This will produce a random value from 0 to 31 since typ is an 8-bit variable 
and the upper limit already covers the maximum value it can hold.
Note that repeated randomization gave all values except the ones that fall within the range 3 through 6.*/
rand bit [2:0] typ;
constraint inv_range { ! (typ inside {[3:6]}); }  // 0~31 中隨機除了 3~6 的值

/*
  # KERNEL: itr=0 typ=7
  # KERNEL: itr=1 typ=0
  # KERNEL: itr=2 typ=7
  # KERNEL: itr=3 typ=0
  # KERNEL: itr=4 typ=0
  # KERNEL: itr=5 typ=0
  # KERNEL: itr=6 typ=7
  # KERNEL: itr=7 typ=1
  # KERNEL: itr=8 typ=1
  # KERNEL: itr=9 typ=7
*/