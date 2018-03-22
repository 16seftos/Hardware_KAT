`timescale 1ns / 1ps

//Taint Testing verilog code

//The input dword is two data which are being acted upon by the ALU
//The monitor should also check that it is an ALU instruction, in later versions
module taint(i, o);
  output [63:0] o;
  reg [63:0] o;
  input [63:0] i;

  reg [63:0] internal0;
  reg [63:0] internal1;
  reg [63:0] internal2;

  always @(*) begin
    internal2 = 0;
    internal1 = 0;
    internal0 = 0;
    o = 0;
    if (((((i >> 63) & (-1 >> 63)) == 1) | (((i >> 31) & (-1 >> 63)) == 1))) begin
      internal2 = (64'h7FFFFFFF7FFFFFFF & i);
      //Check -<large number>?
      internal0 = (64'h8000000080000000 | internal2);
    end else begin
    end
    if (~((((i >> 63) & (-1 >> 63)) == 1) | (((i >> 31) & (-1 >> 63)) == 1))) begin
      internal1 = i;
    end else begin 
    end
    o = (internal0 | internal1);
  end
endmodule