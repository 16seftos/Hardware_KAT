`timescale 1ns / 1ps

//SFI Testing verilog code

module SFI(ri, ro);
  output [63:0] ro;
  reg [63:0] ro;
  input [63:0] ri;

  always @(*) begin
    ro = 0;
    if ((((ri >> 56) & (-1 >> 56)) == 162)) begin
      ro = ri;
    end else begin
    end
  end
endmodule