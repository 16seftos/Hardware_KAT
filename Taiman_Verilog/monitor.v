`define Rzero 5'b00000
`define Ijs 8'h0 
`define Ijf 8'h5 

// Code your design here
module dut(
  input clk,
  input [31:0] pc,
  input [31:0] inst,
  output reg r,
  output reg j);
  
  wire [5:0] opcode = inst[31:26];
  wire [4:0] dest = inst [15:11];
  wire [5:0] funct = inst [5:0];
  wire [25:0] jtarget = inst [25:0];
  wire [4:0] jreg = inst [25:21];
  wire [5:0] mc = inst [20:16];
  wire [3:0] mpc = pc [31:28];
  reg i;
  
  always @(posedge clk) begin
    
    case(opcode)
      6'b000000:begin
        if(dest == `Rzero) begin
          r <= 1;
          j <= 0;
        end
        else if(funct == 6'b001000 && jreg == `Rzero) begin
          r <= 1;
          j <= 1;
        end
      end
      6'b000010,6'b000011: begin
        i = {mpc,jtarget,2'b00};
        if((i >= `Ijs) && (i<`Ijf)) begin
          j <= 1;
          r <= 0;
          end
      end
      6'b010000: begin
        if(mc == `Rzero) begin
          r <= 1;
          j <= 0;
        end
      end
      
      default:begin
        r <= 0;
        j <= 0;
      end
    endcase
  end
endmodule