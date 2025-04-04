# Design-Verification
## System Verilog 環境架設
- **Local environment:**
  ![image](https://github.com/user-attachments/assets/ec80103c-f504-4db7-a466-33e12b753d41)
  https://ithelp.ithome.com.tw/m/articles/10315791  
  https://www.dcard.tw/f/nctu/p/239947030  
  https://www.dcard.tw/f/nctu/p/235935287
  - **編譯與執行**
  ```
  iverilog -o YYY XXX.sv  
  iverilog -o YYY -g2012 XXX.sv (https://electronics.stackexchange.com/questions/640456/syntax-error-iverilog)
  vvp YYY
  ```
  - Current supported generations  
  ![image](https://github.com/user-attachments/assets/ce38d515-bda4-4869-b639-a58ed86026a8)
- **Online environment:**
  ![image](https://github.com/user-attachments/assets/bad19595-3b14-490b-935c-6a4cfa8c5e65)
  https://www.youtube.com/watch?v=f9uwtAax4v0  
- **波形**  
  選取 Open EPWave after run  
  ![481796210_614526054679241_8146042943903981013_n](https://github.com/user-attachments/assets/3ff5448e-e3ac-4010-bd36-cc7783d986d8)
  ![483264664_1216799453199195_1258006194081326055_n](https://github.com/user-attachments/assets/15a664de-0fc3-4ecc-80cd-a2775550d0c6)
## Reference
路科验证: https://www.bilibili.com/video/BV1k7411H7Jo/  
https://www.youtube.com/watch?v=_QjZ06eg3cY&list=PL40xmtPvboRs6Ng_1Q_V-1MdJH50A6Ulz&index=4  
ChipVerify(SystemVerilog): https://www.chipverify.com/systemverilog  
ChipVerify(UVM): [https://www.chipverify.com/systemverilog  ](https://www.chipverify.com/tutorials/uvm)
