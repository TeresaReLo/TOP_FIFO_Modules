/* 
	=========================================================================================
	Module name	: funct_generator
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator.sv
	Type		: SystemVerilog Top
	
	Description	: Function Generator IPCore
                  The module can be parameterized in word size, number of integer and decimal 
                  bits and number of positions in the lut, for this the database for the LUTs 
                  with these new features must be provided.          
	-----------------------------------------------------------------------------------------
	clocks	        : clk
	reset		: async posedge "rst"		
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/
//[INT_BITS-1 : 0-FIXED_POINT_BITS]
module funct_generator #(
	parameter DATA_WIDTH = 32,
        parameter INT_BITS = 4,        
        parameter LUT_ADDR = 8,
        parameter RESET_VALUE=0,
        parameter RESET_AMP=32'h10000000,
        parameter COS_FILE = "sin.txt",
        parameter SIN_FILE = "cos.txt",
        parameter TRIAN_FILE = "triangular.txt",
        parameter SQUA_FILE ="square.txt",
        localparam FIXED_POINT_BITS = (DATA_WIDTH - INT_BITS)
        )(
	//INPUTS
	input  logic 				                clk,
	input  logic 				                rst,
	input  logic 				                en_low_i, 
	input  logic 				                enh_conf_i, 
        input  logic signed  [INT_BITS-1 : 0]	                amp_i,  
	input  logic	     [1:0]	                        sel_i,
	//OUTPUTS
	output logic                                            wr_en_o,
	output logic signed  [DATA_WIDTH-1 : 0]   data_o
);


logic        [LUT_ADDR-1:0] addr, addr_temp;

logic        [DATA_WIDTH-1 : 0]	amp_reg;

logic signed [DATA_WIDTH-1 : 0] cos_temp;
logic signed [DATA_WIDTH-1 : 0] sin_temp;
logic signed [DATA_WIDTH-1 : 0] trian_temp;
logic signed [DATA_WIDTH-1 : 0] squa_temp;

logic signed [DATA_WIDTH-1 : 0] data_select;

logic signed [(DATA_WIDTH*2)-1:0] data_temp;

/************** FSM signals *****************/

bit enh_config_fsm;
bit clrh_addr_fsm;
bit enh_gen_fsm;

bit en_config_amp; 

/***********FSM*****************/
funct_generator_fsm fsm(
    .clk(clk        ),
    .rst(rst        ),
    .en_low_i(en_low_i),
    .enh_conf_i(enh_conf_i),
    .clrh_addr_fsm(clrh_addr_fsm),
    .enh_config_fsm(enh_config_fsm),
    .enh_gen_fsm(enh_gen_fsm)
);
    


/***********LUT sin*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	(SIN_FILE)
)
LUT_sin(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(sin_temp)
);

/***********LUT cos*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	(COS_FILE)
)
LUT_cos(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(cos_temp)
);	

/***********LUT triangular*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	(TRIAN_FILE)
)
LUT_trian(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(trian_temp)
);

/***********LUT square*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	(SQUA_FILE)
)
LUT_squa(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(squa_temp)
);	

/***********MULTIPLICACION AMPLITUD*****************/
funct_generator_multi #(
    .DATA_WIDTH(DATA_WIDTH)
)
amplitud_confi(
    .enh(enh_gen_fsm), 
    .a_i(data_select),
    .b_i(amp_reg),
    .data_o(data_temp)
);

assign data_o = (rst) ? ('0) :((enh_gen_fsm)? data_temp[(DATA_WIDTH*2)-INT_BITS:FIXED_POINT_BITS] : data_o);

//assign data_o = data_temp[32:0];

/***********ADDER ADDRES*****************/
funct_generator_adder #(
    .DATA_WIDTH	(LUT_ADDR)
)
adder_addres(
    .clrh   (clrh_addr_fsm),
    .enh    (enh_gen_fsm),
    .data_a_i(addr),
    .data_b_i({{(LUT_ADDR-1){1'b0}},1'b1}),
    .data_c_i('0),
    .data_o (addr_temp) 	
);


/**********************REGISTER*****************************/

funct_generator_register #(
    .DATA_WIDTH(LUT_ADDR),
    .RESET_VALUE(RESET_VALUE)
)
addr_reg(
    .clk	(clk	    ),
    .rst	(rst	    ),
    .clrh	(enh_config_fsm),
    .enh	(enh_gen_fsm ),
    .d  	(addr_temp  ),
    .q	        (addr       )	
);

funct_generator_register #(
    .DATA_WIDTH(DATA_WIDTH),
    .RESET_VALUE(RESET_AMP)
)
amp_register(
    .clk	(clk	    ),
    .rst	(rst	    ),
    .clrh	(1'b0        ),
    .enh	(en_config_amp),
    .d  	({amp_i, {FIXED_POINT_BITS{1'b0}}}),
    .q	        (amp_reg    )	
);

assign en_config_amp = (enh_config_fsm && (amp_i != '0) && (amp_i != ({1'b1,{(INT_BITS-1){1'b0}}}))); 


/********************MULTIPLEXOR*****************************/

funct_generator_mux #(
    .DATA_WIDTH(DATA_WIDTH)
)mux_signal(
	.sel_i(sel_i), 
        .enh(1'b1),
	.data_0_i(sin_temp),
	.data_1_i(cos_temp),
	.data_2_i(trian_temp),
	.data_3_i(squa_temp),
	.data_o(data_select)
);

assign wr_en_o = (enh_gen_fsm)? 1'b1 : 1'b0;

endmodule
