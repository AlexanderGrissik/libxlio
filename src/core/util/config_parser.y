/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 *
 * $Id: config_parser.y 1.5 2005/06/29 11:39:27 eitan Exp $
 */


/*

*/
%{

/* header section */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <util/libxlio.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <linux/if_ether.h>

typedef enum
{
	CONF_RULE
} configuration_t;

#define YYERROR_VERBOSE 1

extern int yyerror(const char *msg);
extern int yylex(void);
static int parse_err = 0;

struct dbl_lst	__instance_list;

/* some globals to store intermidiate parser state */
static struct use_family_rule __xlio_rule;
static struct address_port_rule *__xlio_address_port_rule = NULL;
static int __xlio_rule_push_head = 0;
static int current_role = 0;
static configuration_t current_conf_type = CONF_RULE;
static struct instance *curr_instance = NULL;

int __xlio_config_empty(void)
{
	return ((__instance_list.head == NULL) && (__instance_list.tail == NULL));
}

/* define the address by 4 integers */
static void __xlio_set_ipv4_addr(short a0, short a1, short a2, short a3)
{
	char buf[16];
	struct in_addr *p_ipv4 = NULL;
  
	p_ipv4 = &(__xlio_address_port_rule->ipv4);
  
	sprintf(buf,"%d.%d.%d.%d", a0, a1, a2, a3);
	if (1 != inet_pton(AF_INET, (const char*)buf, p_ipv4)) {
		parse_err = 1;
		yyerror("provided address is not legal");
	}
}

static void __xlio_set_inet_addr_prefix_len(unsigned char prefixlen)
{
	if (prefixlen > 32)
		prefixlen = 32;
	
	__xlio_address_port_rule->prefixlen = prefixlen;
}

// SM: log part is  not used...
int __xlio_min_level = 9;

void __xlio_dump_address_port_rule_config_state(char *buf) {
	if (__xlio_address_port_rule->match_by_addr) {
		char str_addr[INET_ADDRSTRLEN];

		inet_ntop(AF_INET, &(__xlio_address_port_rule->ipv4), str_addr, sizeof(str_addr));
		if ( __xlio_address_port_rule->prefixlen != 32 ) {
 			sprintf(buf+strlen(buf), " %s/%d", str_addr,
					__xlio_address_port_rule->prefixlen);
		} else {
			sprintf(buf+strlen(buf), " %s", str_addr);
		}
	} else {
		sprintf(buf+strlen(buf), " *");
	}
	
	if (__xlio_address_port_rule->match_by_port) {
		sprintf(buf+strlen(buf), ":%d",__xlio_address_port_rule->sport);
		if (__xlio_address_port_rule->eport > __xlio_address_port_rule->sport) 
			sprintf(buf+strlen(buf), "-%d",__xlio_address_port_rule->eport);
	}
	else
		sprintf(buf+strlen(buf), ":*");
}

/* dump the current state in readable format */
static void  __xlio_dump_rule_config_state() {
	char buf[1024];
	sprintf(buf, "\tACCESS CONFIG: use %s %s %s ", 
			__xlio_get_transport_str(__xlio_rule.target_transport), 
			__xlio_get_role_str(current_role),
			__xlio_get_protocol_str(__xlio_rule.protocol));
	__xlio_address_port_rule = &(__xlio_rule.first);
	__xlio_dump_address_port_rule_config_state(buf);
	if (__xlio_rule.use_second) {
		__xlio_address_port_rule = &(__xlio_rule.second);
		__xlio_dump_address_port_rule_config_state(buf);
	}
	sprintf(buf+strlen(buf), "\n");
	__xlio_log(1, "%s", buf);
}

/* dump configuration properites of new instance */
static void  __xlio_dump_instance() {
	char buf[1024];
	
	if (curr_instance) {
		sprintf(buf, "CONFIGURATION OF INSTANCE ");
		if (curr_instance->id.prog_name_expr)
			sprintf(buf+strlen(buf), "%s ", curr_instance->id.prog_name_expr);
		if (curr_instance->id.user_defined_id)
			sprintf(buf+strlen(buf), "%s", curr_instance->id.user_defined_id);
		sprintf(buf+strlen(buf), ":\n");
		__xlio_log(1, "%s", buf);
	}
}

static void __xlio_add_dbl_lst_node_head(struct dbl_lst *lst, struct dbl_lst_node *node)
{
	if (node && lst) {
	
		node->prev = NULL;
		node->next = lst->head;
		
		if (!lst->head)
			lst->tail = node;
		else 
			lst->head->prev = node;	
					
		lst->head = node;
	}
}

static void __xlio_add_dbl_lst_node(struct dbl_lst *lst, struct dbl_lst_node *node)
{
	if (node && lst) {
		node->prev = lst->tail;
	
		if (!lst->head) 
			lst->head = node;
		else 
			lst->tail->next = node;
		lst->tail = node;
	}
}

static struct dbl_lst_node* __xlio_allocate_dbl_lst_node()
{
	struct dbl_lst_node *ret_val = NULL;
	
	ret_val = (struct dbl_lst_node*) malloc(sizeof(struct dbl_lst_node));
	if (!ret_val) {
		yyerror("fail to allocate new node");
		parse_err = 1;		
	}
	else
		memset((void*) ret_val, 0, sizeof(struct dbl_lst_node));	
	return ret_val;
}

/* use the above state for adding a new instance */
static void __xlio_add_instance(char *prog_name_expr, char *user_defined_id) {
	struct dbl_lst_node *curr, *new_node;
	struct instance *new_instance;
  
	curr = __instance_list.head;
	while (curr) {
		struct instance *instance = (struct instance*)curr->data;
		if (!strcmp(prog_name_expr, instance->id.prog_name_expr) && !strcmp(user_defined_id, instance->id.user_defined_id)) {
			curr_instance = (struct instance*)curr->data;
			if (__xlio_min_level <= 1) __xlio_dump_instance();
			return;  		
		}
		curr = curr->next;
	}
  
	if (!(new_node = __xlio_allocate_dbl_lst_node())) 
		return;
	
	new_instance = (struct instance*) malloc(sizeof(struct instance));
	if (!new_instance) {
		free(new_node);
		yyerror("fail to allocate new instance");
		parse_err = 1;
		return;
	}

	memset((void*) new_instance, 0, sizeof(struct instance));
	new_instance->id.prog_name_expr = strdup(prog_name_expr);
	new_instance->id.user_defined_id = strdup(user_defined_id);
  
	if (!new_instance->id.prog_name_expr || !new_instance->id.user_defined_id) {
		yyerror("failed to allocate memory");
		parse_err = 1;
		if (new_instance->id.prog_name_expr)
			free(new_instance->id.prog_name_expr);
		if (new_instance->id.user_defined_id)
			free(new_instance->id.user_defined_id);
		free(new_instance);
		return;
	}
	new_node->data = (void*)new_instance;
	__xlio_add_dbl_lst_node(&__instance_list, new_node);
	curr_instance = new_instance;
	if (__xlio_min_level <= 1) __xlio_dump_instance();
}

static void __xlio_add_inst_with_int_uid(char *prog_name_expr, int user_defined_id) {
	char str_id[50];
	sprintf(str_id, "%d", user_defined_id);
	__xlio_add_instance(prog_name_expr, str_id);
}

/* use the above state for making a new rule */
static void __xlio_add_rule() {
	struct dbl_lst *p_lst;
	struct use_family_rule *rule;
	struct dbl_lst_node *new_node;

	if (!curr_instance)
		__xlio_add_instance("*", "*");
  	if (!curr_instance)
		return;
  
	if (__xlio_min_level <= 1) __xlio_dump_rule_config_state();
	switch (current_role) {
	case ROLE_TCP_SERVER:
		p_lst = &curr_instance->tcp_srv_rules_lst;
		break;
	case ROLE_TCP_CLIENT:
		p_lst = &curr_instance->tcp_clt_rules_lst;
		break;
	case ROLE_UDP_SENDER:
		p_lst = &curr_instance->udp_snd_rules_lst;
		break;
	case ROLE_UDP_RECEIVER:
		p_lst = &curr_instance->udp_rcv_rules_lst;
		break;
	case ROLE_UDP_CONNECT:
		p_lst = &curr_instance->udp_con_rules_lst;
		break;
	default:
		yyerror("ignoring unknown role");
		parse_err = 1;
		return;
		break;
	}

	if (!(new_node = __xlio_allocate_dbl_lst_node())) 
		return;
	
	rule = (struct use_family_rule *)malloc(sizeof(*rule));
	if (!rule) {
		free(new_node);
		yyerror("fail to allocate new rule");
		parse_err = 1;
		return;
	}
	memset(rule, 0, sizeof(*rule));
	new_node->data = (void*)rule;
	*((struct use_family_rule *)new_node->data) = __xlio_rule; 
	if (__xlio_rule_push_head)
		__xlio_add_dbl_lst_node_head(p_lst, new_node);
	else
		__xlio_add_dbl_lst_node(p_lst, new_node);
}

%}


%union {
  int        ival;
  char      *sval;
}             

%token USE "use"
%token TCP_CLIENT "tcp client"
%token TCP_SERVER "tcp server"
%token UDP_SENDER "udp sender"
%token UDP_RECEIVER "udp receiver"
%token UDP_CONNECT "udp connect"
%token TCP "tcp"
%token UDP "udp"
%token OS "os"
%token XLIO "xlio"
%token SDP "sdp"
%token SA "sa"
%token INT "integer value"
%token APP_ID "application id"
%token PROGRAM "program name"
%token USER_DEFINED_ID_STR "userdefined id str"
%token LOG "log statement"
%token DEST "destination"
%token STDERR "ystderr"
%token SYSLOG "syslog"
%token FILENAME "yfile"
%token NAME "a name"
%token LEVEL "min-level"
%token LINE "new line"
%type <sval> NAME PROGRAM USER_DEFINED_ID_STR
%type <ival> INT LOG DEST STDERR SYSLOG FILENAME APP_ID USE OS XLIO SDP TCP UDP TCP_CLIENT TCP_SERVER UDP_SENDER UDP_RECEIVER UDP_CONNECT LEVEL LINE 
%start config

%{
  long __xlio_config_line_num;
%}
%%

NL:
	  LINE
	| NL LINE
	|;
    
ONL:
	| NL;
    
config: 
	ONL statements
	;

statements:
	| statements statement
	;

statement: 
 	log_statement
	| app_id_statement  
	| socket_statement
	;

log_statement: 
 	LOG log_opts NL
	;

log_opts:
	| log_opts log_dest
	| log_opts verbosity
	;

log_dest: 
 	  DEST STDERR			{ __xlio_log_set_log_stderr(); }
	| DEST SYSLOG			{ __xlio_log_set_log_syslog(); }
  	| DEST FILENAME NAME		{ __xlio_log_set_log_file($3); }
	;
    
verbosity: 
	LEVEL INT { __xlio_log_set_min_level($2); }
	;

app_id_statement:
	app_id NL
	;

app_id:
	  APP_ID PROGRAM USER_DEFINED_ID_STR	{__xlio_add_instance($2, $3);	if ($2) free($2); if ($3) free($3);	}
	| APP_ID PROGRAM INT			{__xlio_add_inst_with_int_uid($2, $3);	if ($2) free($2);		}
	;


socket_statement: 
    use transport role tuple NL { __xlio_add_rule(); }
 	;
 	
use:
	USE { current_conf_type = CONF_RULE; }
 	; 

transport:
 	  OS	{ __xlio_rule.target_transport = TRANS_OS;	}
	| XLIO	{ __xlio_rule.target_transport = TRANS_XLIO;	}
	| SDP	{ __xlio_rule.target_transport = TRANS_SDP;	}
	| SA	{ __xlio_rule.target_transport = TRANS_SA;	}
	| '*'	{ __xlio_rule.target_transport = TRANS_ULP;	}
	;


role:
	  TCP_SERVER	{ current_role = ROLE_TCP_SERVER; 	__xlio_rule.protocol = PROTO_TCP; }
	| TCP_CLIENT 	{ current_role = ROLE_TCP_CLIENT; 	__xlio_rule.protocol = PROTO_TCP; }
	| UDP_RECEIVER	{ current_role = ROLE_UDP_RECEIVER; __xlio_rule.protocol = PROTO_UDP; }
	| UDP_SENDER 	{ current_role = ROLE_UDP_SENDER;	__xlio_rule.protocol = PROTO_UDP; }
	| UDP_CONNECT 	{ current_role = ROLE_UDP_CONNECT;	__xlio_rule.protocol = PROTO_UDP; }
	;

tuple:
	  three_tuple
	| five_tuple
	;

three_tuple:
	address_first ':' ports
	;

five_tuple:
	address_first ':' ports ':' address_second ':' ports
	;

address_first:
	{ __xlio_address_port_rule = &(__xlio_rule.first); __xlio_rule.use_second = 0; } address
	;

address_second:
	{ __xlio_address_port_rule = &(__xlio_rule.second); __xlio_rule.use_second = 1; } address
	;

address:
	  ipv4         { if (current_conf_type == CONF_RULE) __xlio_address_port_rule->match_by_addr = 1; __xlio_set_inet_addr_prefix_len(32); }
	| ipv4 '/' INT { if (current_conf_type == CONF_RULE) __xlio_address_port_rule->match_by_addr = 1; __xlio_set_inet_addr_prefix_len($3); }
	| '*'          { if (current_conf_type == CONF_RULE) __xlio_address_port_rule->match_by_addr = 0; __xlio_set_inet_addr_prefix_len(32); }
	;

ipv4:
	INT '.' INT '.' INT '.' INT { __xlio_set_ipv4_addr($1,$3,$5,$7); }
 	;

ports:
	  INT         { __xlio_address_port_rule->match_by_port = 1; __xlio_address_port_rule->sport= $1; __xlio_address_port_rule->eport= $1; }
	| INT '-' INT { __xlio_address_port_rule->match_by_port = 1; __xlio_address_port_rule->sport= $1; __xlio_address_port_rule->eport= $3; }
	| '*'         { __xlio_address_port_rule->match_by_port = 0; __xlio_address_port_rule->sport= 0;  __xlio_address_port_rule->eport= 0;  }
	;

%%

int yyerror(const char *msg)
{
	/* replace the $undefined and $end if exists */
	char *orig_msg = (char*)malloc(strlen(msg)+25);
	char *final_msg = (char*)malloc(strlen(msg)+25);

	strcpy(orig_msg, msg);
	
	char *word = strtok(orig_msg, " ");
	final_msg[0] = '\0';
	while (word != NULL) {
		if (!strncmp(word, "$undefined", 10)) {
			strcat(final_msg, "unrecognized-token ");
		} else if (!strncmp(word, "$end",4)) {
			strcat(final_msg, "end-of-file ");
		} else {
			strcat(final_msg, word);
			strcat(final_msg, " ");
		}
		word = strtok(NULL, " ");
	}
	
	__xlio_log(9, "Error (line:%ld) : %s\n", __xlio_config_line_num, final_msg);
	parse_err = 1;
	
	free(orig_msg);
	free(final_msg);
	return 1;
}

#include <unistd.h>
#include <errno.h>

/* parse apollo route dump file */
int __xlio_parse_config_file (const char *fileName) {
	extern FILE * libxlio_yyin;
   
	/* open the file */
	if (access(fileName, R_OK)) {
		printf("libxlio Error: No access to open File:%s %s\n", 
				fileName, strerror(errno));
		return(1);
	}

	libxlio_yyin = fopen(fileName,"r");
	if (!libxlio_yyin) {
		printf("libxlio Error: Fail to open File:%s\n", fileName);
		return(1);
	}
	__instance_list.head = NULL;
	__instance_list.tail = NULL;
	parse_err = 0;
	__xlio_config_line_num = 1;

	/* parse it */
	yyparse();

	fclose(libxlio_yyin);
	return(parse_err);
}

int __xlio_parse_config_line (char *line) {
	extern FILE * libxlio_yyin;
	
	__xlio_rule_push_head = 1;
	
	libxlio_yyin = fmemopen(line, strlen(line), "r");
	
	if (!libxlio_yyin) {
		printf("libxlio Error: Fail to parse line:%s\n", line);
		return(1);
	}
	
	parse_err = 0;
	yyparse();
	
	fclose(libxlio_yyin);
	
	return(parse_err);
}
