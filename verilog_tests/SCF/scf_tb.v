`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   15:43:59 03/23/2018
// Design Name:   SCF
// Module Name:   /home/seaghan/Desktop/SecKat/verilog_tests/SCF/xilinx/scf/scf_tb.v
// Project Name:  scf
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: SCF
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module scf_tb;

  // Inputs
  reg [63:0] i;

  // Outputs
  wire [63:0] o;

  reg [63:0] exp_o;
  reg all_pass;

  // Instantiate the Unit Under Test (UUT)
  SCF uut (
    .i(i), 
    .o(o)
  );

  initial begin
    // Initialize Inputs
    i = 0;
    exp_o = 0;
    all_pass = 1;

    // Wait 10 ns for global reset to finish
    #10;
        
    //remember: intr lower 32 bits, data higher 32

    // Add stimulus here
    $monitor("\nTesting");#1;
    $monitor("\nTesting nonCF instructions:");
      //these are from other programs I wrote, or random inputs
      i     <= 32'h00000820;
      exp_o <= 32'h00000820;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 32'h04FFFFFF;
      exp_o <= 32'h04FFFFFF;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 32'h00051820;
      exp_o <= 32'h00051820;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 32'h00FFFF1C;
      exp_o <= 32'h00FFFF1C;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 32'h2824000A;
      exp_o <= 32'h2824000A;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 32'h20210001;
      exp_o <= 32'h20210001;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 32'h00000000;
      exp_o <= 32'h00000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
    #10;
	 
	 $monitor("\nTesting R type (unsatisfactory):");
      //should be filtered:
		i     <= 64'h0000000010000000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 64'h000000001C000000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 64'h0000000018000000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 64'h0000000014000000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 32'h08000000;
      exp_o <= 32'h00000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 32'h0C000000;
      exp_o <= 32'h00000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
	$monitor("(satisfactory)");#1;
		//should pass:
		i     <= 64'h0000000110000001;
      exp_o <= 64'h0000000110000001;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 64'h000000021C000002;
      exp_o <= 64'h000000021C000002;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 64'h0000000318000003;
      exp_o <= 64'h0000000318000003;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 64'h0000000414000004;
      exp_o <= 64'h0000000414000004;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 32'h08000005;
      exp_o <= 32'h08000005;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
		i     <= 32'h0C000006;
      exp_o <= 32'h0C000006;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
		#1;
	 #10;
	 
	 $monitor("\nTesting Reg_Imm instructions (unsatisfactory):");
      //0000.01 00.000 0.0000. 00000 00000 000000
		//04xx0000
		i     <= 64'h0000000004010000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'h0000000004110000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'h0000000004000000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'h0000000004100000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
	$monitor("(satisfactory)");#1;
		i     <= 64'h0000000104010000;
      exp_o <= 64'h0000000104010000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'h0000000204110000;
      exp_o <= 64'h0000000204110000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'h0000000304000000;
      exp_o <= 64'h0000000304000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'h0000000404100000;
      exp_o <= 64'h0000000404100000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
    #10;
	 
	 $monitor("\nTesting Reg_Imm instructions (unsatisfactory):");
      //0000.01 00.000 0.0000. 00000 00000 000000
		//04xx0000
		i     <= 64'h0000000000000009;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'h0000000000000008;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
	$monitor("(satisfactory)");#1;
		i     <= 64'hF000000100000009;
      exp_o <= 64'hF000000100000009;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
		i     <= 64'hF000000200000008;
      exp_o <= 64'hF000000200000008;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
    #10;
    
   
  //FINISHED TESTING
    $monitor("\nDone testing, exiting\n");#1;
    if(all_pass == 1) begin
      $monitor("All Pass");#1;
    end else begin
      $monitor("Not all pass");#1;
    end
    $finish();    
  end
      
endmodule

