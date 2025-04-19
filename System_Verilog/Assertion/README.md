# SVA
```
always_comb
begin
  a_ia: assert (a && b);
end
```
* 只有 a 或 b 發生變化時去 assertion 做檢查
![image](https://github.com/user-attachments/assets/89a300b5-9ef0-40c0-b323-c4c5401f115b)  
```
a_cc: assert property(@(posedge clk)
                                    not (a && b));
```
![image](https://github.com/user-attachments/assets/399a1456-b3b4-413d-80cc-966f780758ca)  
```
sequence s2;
  @(poseedge clk) $rose(a);  // 上一拍為低, 這拍為高
endsequence
```
![image](https://github.com/user-attachments/assets/098136e4-35ef-4686-80d0-3e1a4fc909fe)  
為甚麼不是 timestamp 1 的時候呢?  
因為 a 是因為 posedge 才驅動的, 所以一定會 posedge 之後 a 才拉起來, 所以在 timestamp 1 時 a 為 0  
```
sequence s3;
  @(poseedge clk) a || b;
endsequence
```
![image](https://github.com/user-attachments/assets/84a2b63c-6cb2-4f6f-b9d6-cf80065e5c04)  
這裡要看時鐘 posedge 左邊的值才採樣的值  
```
sequence s4;
  @(poseedge clk) a ##2 b;  // 當前採樣的 a 為高, 兩拍後 b 也採樣為高
endsequence
```
![image](https://github.com/user-attachments/assets/4b05dac5-66cc-45ee-b04c-cc4fda103690)  
```
sequence s6;
  @(poseedge clk) a ##2 b;  // 當前採樣的 a 為高, 兩拍後 b 也採樣為高
endsequence

property p6;
  not s6;
endproperty

a6: assert property(p6);
```
![image](https://github.com/user-attachments/assets/9931da76-b2c0-48d1-aa57-e4db8dcc0828)  
![image](https://github.com/user-attachments/assets/d2f65df9-2ad8-437f-ae2b-26df06cb3cd8)  
## Implication
```
property p8;
  @(poseedge clk) a |-> b;  // 在先行條件滿足時 (a), 在同一拍看後續表達式是否也滿足 (b)
endproperty

a8: assert property(p8);
```
![image](https://github.com/user-attachments/assets/9ceb345b-990d-461b-aef6-8f0c8772d7af)  
```
property p9;
  @(poseedge clk) a |=> b;  // 在先行條件滿足時 (a), 在下一拍看後續表達式是否也滿足 (b)
endproperty

a9: assert property(p9);
```
![image](https://github.com/user-attachments/assets/e03d2e75-ec96-45ec-b198-aa51bb25f3f7)  
```
property p12;
  @(poseedge clk) (a && b) |-> ##[1:3] c;  // 在任何一拍看 a 和 b 是否同時為高, 接下來 1 到 3 拍之間, c 應該至少在一個時間周期內為高
endproperty

a12: assert property(p12);
```
![image](https://github.com/user-attachments/assets/783817b2-8a29-4540-9245-3b13d0288680)  
```
property p13;
  @(poseedge clk) a |-> ##[1:$] b #[0:$] c;  // 無限時序 (不建議使用)
endproperty

a13: assert property(p13);
```
![image](https://github.com/user-attachments/assets/cd61df9e-0f3e-485b-92ef-36c6177fd117)  
```
sequence s15a;
  @(poseedge clk) a ##1 b;
endsequence

sequence s15b;
  @(poseedge clk) c ##1 d;
endsequence

property p15a;
  s15a |=> s15b;
endproperty

property p15b;
  s15a.ended |-> ##2 s15b.ended;  // 前一個 sequence 結束的點當作連接點, s15a 結束的點, 就是延遲的第一拍
endproperty

// s15a 和 s15b 是同樣的意思

a15a: assert property(p15a);
a15b: assert property(p15b);
```
```
property p17;
  @(poseedge clk) c ? d == a : d == b;
endproperty

a17: assert property(p17);
```
![image](https://github.com/user-attachments/assets/4968979c-4931-48f0-a14b-f32afa971da5)  
# $past
![image](https://github.com/user-attachments/assets/24153a20-0169-4cbd-a70a-b63c055e82d8)  
![image](https://github.com/user-attachments/assets/61c8927f-57b7-4cc2-a164-a1973357c8b1)  

# 連續重複運算
![image](https://github.com/user-attachments/assets/f421d00e-317a-4842-9e86-8d25e8766aab)  
![image](https://github.com/user-attachments/assets/77386488-61fe-4874-974e-13f7da8adf0e)  
![image](https://github.com/user-attachments/assets/9e2df2ed-ec59-4b62-b717-226f7a788a40)  
![image](https://github.com/user-attachments/assets/c5822bbf-42d3-432e-bb55-58285678cb32)  
![image](https://github.com/user-attachments/assets/214202ee-ccb7-4d58-be4c-17c796dd28f0)  

# 非連續跟隨重複
![image](https://github.com/user-attachments/assets/b5b7898f-cdc8-48a8-a25d-6f97f0ac0a6b)  
![image](https://github.com/user-attachments/assets/2b31cda3-b233-4a4b-8e8e-8d0dd18cdec7)  
a 三次拉起後, 緊接著 ##1
# 非連續非跟隨重複
![image](https://github.com/user-attachments/assets/7072c071-3c3c-49e9-b8fc-dd0b30aefea3)  
![image](https://github.com/user-attachments/assets/dd1779e5-8266-4b67-a6b0-fdcef5a8377d)  
a 拉高三次後有多隔一拍, 才 ##1

# And
![image](https://github.com/user-attachments/assets/001d9ed2-9f96-45cf-ba2c-bc93e52994ce)  
![image](https://github.com/user-attachments/assets/a5139046-4143-4441-8f78-3d601337fcc9)  

# Intersect
![image](https://github.com/user-attachments/assets/f388f57d-9028-4c29-ad07-eed589916f01)
![image](https://github.com/user-attachments/assets/efef1abb-00aa-4133-9f03-81a58bdec27d)  
![image](https://github.com/user-attachments/assets/6f34291a-2d4a-44b5-8723-68f92836ae77)  

# Or
![image](https://github.com/user-attachments/assets/6e1a8594-6345-4a4e-a9ff-7876815cdfbe)  
![image](https://github.com/user-attachments/assets/138391c3-8823-4c7d-9bbf-2a76acc390c4)  

# first_match
![image](https://github.com/user-attachments/assets/4b6fc907-a67b-49d4-831c-8a4d9563f5a0)  
![image](https://github.com/user-attachments/assets/0097e673-bf67-4043-9272-0ac321bd8c9e)  

# throughout
某條件或是某信號要一直為高
![image](https://github.com/user-attachments/assets/1203b0c5-bfca-4926-bddf-bf34e9001b2a)  
![image](https://github.com/user-attachments/assets/e746db31-3153-40c2-9a46-7bacfe772ce8)  
![image](https://github.com/user-attachments/assets/e01b1ce7-64fe-4ff1-9988-8ac96a3052a2)  

# Within
![image](https://github.com/user-attachments/assets/9ad18c59-6975-4c1d-87ae-e96d9174944c)  
![image](https://github.com/user-attachments/assets/79542841-0c5b-47cd-94ab-e112da6720c2)  

