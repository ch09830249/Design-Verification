# Fork
In verilog, each of the initial and always blocks are spawned off as separate threads that start to run in parallel from zero time. A fork join block also creates different threads that run in parallel.
![image](https://github.com/user-attachments/assets/f87fb4ce-7ad6-4f8d-ab26-33ab62ba4a9d)  
fork join	- Finishes when all child threads are over  
fork join_any -	Finishes when any child thread gets over  
fork join_none -	Finishes soon after child threads are spawned  
