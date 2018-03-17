`timescale 1ns / 1ps

//SFI Testing verilog code

module SFI(ri, ro);
  output [63:0] ro;
  reg [63:0] ro;
  input [63:0] ri;

  always @(*) begin
    ro = 0;
    //How does verilog/Xilinx know that -1 is 64bit?
    if ((((ri >> 56) & (-1 >> 56)) == 162)) begin
      ro = ri;
    end else begin
    end
  end
endmodule