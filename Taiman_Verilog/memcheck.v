`define Ijs 8'h0 
`define Ijf 8'h4

// Code your design here
module memcheck(
  input wire clk,
  input wire [31:0] addr,       // Memory Address
  input wire memwrite, memread,
  output reg rd, w);
  
  //wire [31:0] address = addr [31:0];
  
  always @(posedge clk) begin
    if((addr[31:0] >= `Ijs) && (addr[31:0] <= `Ijf)) begin
      if(memwrite == 1'b1) begin
        w <= 1;
        rd <= 0;
      end
      if(memread == 1'b1) begin
        rd <= 1;
        w <= 0;
      end
    end
       else begin
         w <= 0;
         rd <= 0;
       end
       end
       endmodule
       