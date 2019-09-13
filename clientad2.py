#!/usr/bin/env python
# -*- coding: utf-8 -*- 

'''
Created on 28.03.2013

@author: isidorov
'''
 
import os
import sys
import pygtk
import pty
import gobject
from time import sleep
pygtk.require('2.0')
import time
import threading
import datetime
import gtk
import ldap
import paramiko
from scp import SCPClient
import re
import urllib
import gnomekeyring as gk
import string
import random
import base64
import md5
import pango
import vte
import glib


#----------------------------------------------------------- GLOBAL VARIABLES ----------------------------

dirpath = os.path.realpath(os.path.dirname(sys.argv[0]))
ldap_host = 'XXXX.XXX.XX'
ldap_port = '389'
ldap_mirrors = 'XXXXX.XXX.XX'
SYSLOG_SERVER = 'XXXXX.XXX.XX'
#++++++++++++++++++++++++++++++++++++++++++++++++



#----------------------------------- TextView ----------------------------------------------------------------------
DEFAULT_STYLES = {
    'DEFAULT':      {'font': 'monospace'},
    'comment':      {'foreground': '#0000FF'},
    'preprocessor': {'foreground': '#A020F0'},
    'keyword':      {'foreground': '#A52A2A',
                     'weight': pango.WEIGHT_BOLD},
    'special':      {'foreground': 'turquoise'},
    'mark1':        {'foreground': '#008B8B'},
    'mark2':        {'foreground': '#6A5ACD'},
    'string':       {'foreground': '#FF00FF'},
    'number':       {'foreground': '#FF00FF'},
    'datatype':     {'foreground': '#2E8B57',
                     'weight': pango.WEIGHT_BOLD},
    'function':     {'foreground': '#008A8C'},

    'link':         {'foreground': '#0000FF',
                     'underline': pango.UNDERLINE_SINGLE}}

# defines default-search paths for syntax-files 
SYNTAX_PATH = [ os.path.join('.', 'syntax'),
                dirpath,
                os.path.join(os.path.expanduser('~'),".pygtkcodebuffer"),
                os.path.join(sys.prefix,"share","pygtkcodebuffer","syntax")]

        
class LanguageDefinition:
    """ This class is a container class for all rules (Pattern, KeywordList, 
        ...) specifying the language. You have to used this class if you like
        to hard-code your syntax-definition. """
        
    def __init__(self, rules):
        """ The constructor takes only one argument: A list of rules (i.e 
            Pattern, KeywordList and String). """
        self._grammar = rules
        self._styles = dict()
                
                
    def __call__(self, buf, start, end=None):
        # if no end given -> end of buffer
        if not end: end = buf.get_end_iter()
    
        mstart = mend = end
        mtag   = None
        txt = buf.get_slice(start, end)    
        
        # search min match
        for rule in self._grammar:
            # search pattern
            m = rule(txt, start, end)            
            if not m: continue
            
            # prefer match with smallest start-iter 
            if m[0].compare(mstart) < 0:
                mstart, mend = m
                mtag = rule.tag_name
                continue
            
            if m[0].compare(mstart)==0 and m[1].compare(mend)>0:
                mstart, mend = m
                mtag = rule.tag_name
                continue

        return (mstart, mend, mtag)                


    def get_styles(self):
        return self._styles

        
        
class Pattern:
    """ More or less internal used class representing a pattern. You may use 
        this class to "hard-code" your syntax-definition. """

    def __init__(self, regexp, style="DEFAULT", group=0, flags=""):
        """ The constructor takes at least on argument: the regular-expression.
            
            The optional kwarg style defines the style applied to the string
            matched by the regexp. 
            
            The kwarg group may be used to define which group of the regular 
            expression will be used for highlighting (Note: This means that only
            the selected group will be highlighted but the complete pattern must
            match!)
            
            The optional kwarg flags specifies flags for the regular expression.
            Look at the Python lib-ref for a list of flags and there meaning."""
        # assemble re-flag
        flags += "ML"; flag   = 0
        
#        _log_debug("init rule %s -> %s (%s)"%(regexp, style, flags))
        
        for char in flags:
            if char == 'M': flag |= re.M
            if char == 'L': flag |= re.L
            if char == 'S': flag |= re.S
            if char == 'I': flag |= re.I
            if char == 'U': flag |= re.U
            if char == 'X': flag |= re.X

        # compile re        
        try: self._regexp = re.compile(regexp, flag)
        except re.error, e: 
            raise Exception("Invalid regexp \"%s\": %s"%(regexp,str(e)))

        self._group  = group
        self.tag_name = style
        
        
    def __call__(self, txt, start, end):
        m = self._regexp.search(txt)
        if not m: return None
        
        mstart, mend = m.start(self._group), m.end(self._group)
        s = start.copy(); s.forward_chars(mstart)
        e = start.copy(); e.forward_chars(mend)
        
        return (s,e)    
    


class KeywordList(Pattern):
    """ This class may be used for hard-code a syntax-definition. It specifies 
        a pattern for a keyword-list. This simplifies the definition of 
        keyword-lists. """

    def __init__(self, keywords, style="keyword", flags=""):
        """ The constructor takes at least on argument: A list of strings 
            specifying the keywords to highlight. 
            
            The optional kwarg style specifies the style used to highlight these
            keywords. 
            
            The optional kwarg flags specifies the flags for the 
            (internal generated) regular-expression. """
        regexp = "(?:\W|^)(%s)\W"%("|".join(keywords),)
        Pattern.__init__(self, regexp, style, group=1, flags=flags)
        
        
class String:
    """ This class may be used to hard-code a syntax-definition. It simplifies 
        the definition of a "string". A "string" is something that consists of
        a start-pattern and an end-pattern. The end-pattern may be content of 
        the string if it is escaped. """

    def __init__(self, starts, ends, escape=None, style="string"):
        """ The constructor needs at least two arguments: The start- and 
            end-pattern. 
            
            The optional kwarg escape specifies a escape-sequence escaping the 
            end-pattern.
            
            The optional kwarg style specifies the style used to highlight the
            string. """
        try:
            self._starts  = re.compile(starts)
        except re.error, e: 
            raise Exception("Invalid regexp \"%s\": %s", str(e))
        
        if escape:
            end_exp = "[^%(esc)s](?:%(esc)s%(esc)s)*%(end)s"
            end_exp = end_exp%{'esc':escape*2,'end':ends}
        else:
            end_exp = ends

        try:     
            self._ends    = re.compile(end_exp)
        except re.error, e: 
            raise Exception("Invalid regexp \"%s\": %s", str(e))

        self.tag_name = style


    def __call__(self, txt, start, end):
        start_match = self._starts.search(txt)
        if not start_match: return
        
        start_it = start.copy()
        start_it.forward_chars(start_match.start(0))
        end_it   = end.copy()
        
        end_match = self._ends.search(txt, start_match.end(0)-1)
        if end_match:
            end_it.set_offset(start.get_offset()+end_match.end(0))            
            
        return  start_it, end_it

                            
    # Dispatch start/end - document/element and chars        
    def startDocument(self):
        self.__stack   = []
                
    def endDocument(self):
        del self.__stack
        
    def startElement(self, name, attr):
        self.__stack.append( (name, attr) )
        if hasattr(self, "start_%s"%name):
            handler = getattr(self, "start_%s"%name)
            handler(attr)
    
    def endElement(self, name):
        if hasattr(self, "end_%s"%name):
            handler = getattr(self, "end_%s"%name)
            handler()
        del self.__stack[-1]

    def characters(self, txt):
        if not self.__stack: return
        name, attr = self.__stack[-1]
        
        if hasattr(self, "chars_%s"%name):
            handler = getattr(self, "chars_%s"%name)
            handler(txt)
            

    # Handle regexp-patterns
    def start_pattern(self, attr):
        self.__pattern = ""
        self.__group   = 0
        self.__flags   = ''
        self.__style   = attr['style']
        if 'group' in attr.keys(): self.__group = int(attr['group'])
        if 'flags' in attr.keys(): self.__flags = attr['flags']
        
    def end_pattern(self):
        rule = Pattern(self.__pattern, self.__style, self.__group, self.__flags)
        self._grammar.append(rule)
        del self.__pattern
        del self.__group
        del self.__flags
        del self.__style
        
    def chars_pattern(self, txt):
        self.__pattern += unescape(txt)
                    

    # handle keyword-lists
    def start_keywordlist(self, attr):
        self.__style = "keyword"
        self.__flags = ""
        if 'style' in attr.keys():
            self.__style = attr['style']
        if 'flags' in attr.keys():
            self.__flags = attr['flags']
        self.__keywords = []
        
    def end_keywordlist(self):
        kwlist = KeywordList(self.__keywords, self.__style, self.__flags)
        self._grammar.append(kwlist)
        del self.__keywords
        del self.__style
        del self.__flags
        
    def start_keyword(self, attr):
        self.__keywords.append("")
    
    def end_keyword(self):
        if not self.__keywords[-1]:
            del self.__keywords[-1]
                
    def chars_keyword(self, txt):
        parent,pattr = self.__stack[-2]
        if not parent == "keywordlist": return
        self.__keywords[-1] += unescape(txt)


    #handle String-definitions
    def start_string(self, attr):
        self.__style = "string"
        self.__escape = None
        if 'escape' in attr.keys():
            self.__escape = attr['escape']
        if 'style' in attr.keys():
            self.__style = attr['style']
        self.__start_pattern = ""
        self.__end_pattern = ""

    def end_string(self):
        strdef = String(self.__start_pattern, self.__end_pattern,
                        self.__escape, self.__style)
        self._grammar.append(strdef)
        del self.__style
        del self.__escape
        del self.__start_pattern
        del self.__end_pattern
        
    def chars_starts(self, txt):
        self.__start_pattern += unescape(txt)
        
    def chars_ends(self, txt):
        self.__end_pattern += unescape(txt)


    # handle style
    def start_style(self, attr):
        self.__style_props = dict()
        self.__style_name = attr['name']
        
    def end_style(self):
        self._styles[self.__style_name] = self.__style_props
        del self.__style_props
        del self.__style_name
        
    def start_property(self, attr):
        self.__style_prop_name = attr['name']
        
    def chars_property(self, value):
        value.strip()
        
        # convert value
        if self.__style_prop_name in ['font','foreground','background',]:
            pass
            
        elif self.__style_prop_name == 'variant':
            if not value in self.style_variant_table.keys():
                Exception("Unknown style-variant: %s"%value)
            value = self.style_variant_table[value]
                
        elif self.__style_prop_name == 'underline':
            if not value in self.style_underline_table.keys():
                Exception("Unknown underline-style: %s"%value)
            value = self.style_underline_table[value]
                
        elif self.__style_prop_name == 'scale':
            if not value in self.style_scale_table.keys():
                Exception("Unknown scale-style: %s"%value)
            value = self.style_scale_table[value]

        elif self.__style_prop_name == 'weight':
            if not value in self.style_weight_table.keys():
                Exception("Unknown style-weight: %s"%value)
            value = self.style_weight_table[value]
                
        elif self.__style_prop_name == 'style':
            if not value in self.style_style_table[value]:
                Exception("Unknwon text-style: %s"%value)
            value = self.style_style_table[value]
                
        else:
            raise Exception("Unknown style-property %s"%self.__style_prop_name)

        # store value            
        self.__style_props[self.__style_prop_name] = value
                        
            
class CodeBuffer(gtk.TextBuffer):
    """ This class extends the gtk.TextBuffer to support syntax-highlighting. 
        You can use this class like a normal TextBuffer. """
        
    def __init__(self, table=None, lang=None, styles={}):
        """ The constructor takes 3 optional arguments. 
        
            table specifies a tag-table associated with the TextBuffer-instance.
            This argument will be passed directly to the constructor of the 
            TextBuffer-class. 
            
            lang specifies the language-definition. You have to load one using
            the SyntaxLoader-class or you may hard-code your syntax-definition 
            using the LanguageDefinition-class. 
            
            styles is a dictionary used to extend or overwrite the default styles
            provided by this module (DEFAULT_STYLE) and any language specific 
            styles defined by the LanguageDefinition. """
        gtk.TextBuffer.__init__(self, table)

        # default styles    
        self.styles = DEFAULT_STYLES
                       
        # update styles with lang-spec:
        if lang:
            self.styles.update(lang.get_styles())               
        # update styles with user-defined
        self.styles.update(styles)
        
        # create tags
        for name, props in self.styles.items():
            style = dict(self.styles['DEFAULT'])    # take default
            style.update(props)                     # and update with props
            self.create_tag(name, **style)
        
        # store lang-definition
        self._lang_def = lang
        
        self.connect_after("insert-text", self._on_insert_text)
        self.connect_after("delete-range", self._on_delete_range)
        self.connect('apply-tag', self._on_apply_tag)
        
        self._apply_tags = False
                
                
    def _on_apply_tag(self, buf, tag, start, end):
        # FIXME This is a hack! It allows apply-tag only while
        #       _on_insert_text() and _on_delete_range()
        if not self._apply_tags:
            self.emit_stop_by_name('apply-tag')
            return True
            
                            
    def _on_insert_text(self, buf, it, text, length):
        # if no syntax defined -> nop
        if not self._lang_def: return False
        
        it = it.copy()
        it.backward_chars(length)
        
        if not it.begins_tag():
            it.backward_to_tag_toggle(None)

        if it.begins_tag(self.get_tag_table().lookup("DEFAULT")):
            it.backward_to_tag_toggle(None)
            
        self._apply_tags = True    
        self.update_syntax(it)        
        self._apply_tags = False
        
        
    def _on_delete_range(self, buf, start, end):
        # if no syntax defined -> nop
        if not self._lang_def: return False

        start = start.copy()
        if not start.begins_tag():
            start.backward_to_tag_toggle(None)
    
        self._apply_tags = True                
        self.update_syntax(start)        
        self._apply_tags = False
        
    
    def update_syntax(self, start, end=None):
        """ More or less internal used method to update the 
            syntax-highlighting. """
        # if no lang set    
        if not self._lang_def: return             
            
        # if not end defined
        if not end: end = self.get_end_iter()
        
        # We do not use recursion -> long files exceed rec-limit!
        finished = False
        while not finished: 
            # search first rule matching txt[start..end]            
            mstart, mend, tagname = self._lang_def(self, start, end)

            # optimisation: if mstart-mend is allready tagged with tagname 
            #   -> finished
            if tagname:     #if something found
                tag = self.get_tag_table().lookup(tagname)
                if mstart.begins_tag(tag) and mend.ends_tag(tag) and not mstart.equal(start):
                    self.remove_all_tags(start,mstart)
                    self.apply_tag_by_name("DEFAULT", start, mstart)
                    # finish
                    finished = True
                    continue
                    
            # remove all tags from start..mend (mend == buffer-end if no match)        
            self.remove_all_tags(start, mend)
            # make start..mstart = DEFAUL (mstart == buffer-end if no match)
            if not start.equal(mstart):
                self.apply_tag_by_name("DEFAULT", start, mstart)                
        
            # nothing found -> finished
            if not tagname: 
                finished = True
                continue
        
            # apply tag
            self.apply_tag_by_name(tagname, mstart, mend)

            start = mend
            
            if start == end: 
                finished = True                 
                continue
                
        
    def reset_language(self, lang_def):
        """ Reset the currently used language-definition. """
        # remove all tags from complete text
        start = self.get_start_iter()
        self.remove_all_tags(start, self.get_end_iter())
        # store lexer
        self._lang_def = lang_def
        # update styles from lang_def:
        if self._lang_def:
            self.update_styles(self._lang_def.get_styles())
        # and ...
        self._apply_tags = True
        self.update_syntax(start)
        self._apply_tags = False
        
        
    def update_styles(self, styles):
        """ Update styles. This method may be used to reset any styles at
            runtime. """
        self.styles.update(styles)
        
        table = self.get_tag_table()
        for name, props in styles.items():
            style = self.styles['DEFAULT']
            style.update(props)
            # if tagname is unknown:
            if not table.lookup(name):
                self.create_tag(name, **style) 
            else: # update tag
                tag = table.lookup(name)
                map(lambda i: tag.set_property(i[0],i[1]), style.items())

#=================================== TextView +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++


#--------------------- Other Classes ================================

class ThreadPgClusterInstall(threading.Thread):
    clustername = ''
    hostname = ''
    port = 0
    pgversion = ''
    pgclusterparams = {}
    instsoftonly = False
    

    def __init__(self, hostname, port, clustername, pgversion, instsoftonly, pgclusterparams):
        self.clustername = clustername
        self.hostname = hostname
        self.port = port
        self.pgversion = pgversion
        self.instsoftonly = instsoftonly
        self.pgclusterparams = pgclusterparams
        
        threading.Thread.__init__(self)
        self.threadID = 2
        self.name = 'PgClusterInstall'
        self.counter = 2

    def run(self):
        stdOut.write("Starting install " + self.name + " at " + str(time.strftime('%H:%M:%S')) + '\n')
        pgi = PgClusterInstaller(self.hostname, self.port, self.clustername, self.pgversion, self.instsoftonly, self.pgclusterparams)
        pgi.ldif2LDAP = {}
        if pgi.install() == 0:
            if not self.instsoftonly:
                pgi.registerPgClusterLDAP()
                sleep(5)
                if pgi.startDB('start') == 0:
                    pgi.installPgContribs('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion)
                    pgi.createTempTablespace()
                    pgi.addAdminStatUsers()
            else:
                pgi.installPgContribs('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion)
    
                if self.clustername[:5] == 'stdb_':
                    pgi.startDB('stop')
                    pgi.registerPgClusterAsStandby()
                        
        stdOut.write("Exiting PgCluster install" + self.name + " at " + str(time.strftime('%H:%M:%S')) + '\n')
                
                
class ThreadPgClusterUpgrade(threading.Thread):
    clustername = ''
    hostname = ''
    port = 0
    pgversion = ''
    pgclusterparams = {}

    def __init__(self, hostname, port, clustername, pgversion, preinstsoft, pgclusterparams):
        self.clustername = clustername
        self.hostname = hostname
        self.port = port
        self.pgversion = pgversion
        self.pgclusterparams = pgclusterparams
        self.preinstsoft = preinstsoft
        
        threading.Thread.__init__(self)
        self.threadID = 6
        self.name = 'PgClusterUpgrade'
        self.counter = 6

    def run(self):
        stdOut.write("Starting upgrade " + self.name + " at " + str(time.strftime('%H:%M:%S')) + '\n')
        pgi = PgClusterInstaller(self.hostname, self.port, self.clustername, self.pgversion, True, self.pgclusterparams)
        self.getObjectDetailFromLDAP = pgi.getObjectDetailFromLDAP
        if self.preinstsoft:
            if pgi.install() == 0:
                pgi.installPgContribs('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion)
        
        if (tuple(map(int, self.pgversion.split('.')))[1] == self.getCurrentPgVer()[1]) and (tuple(map(int, self.pgversion.split('.')))[0] == self.getCurrentPgVer()[0]):
            if tuple(map(int, self.pgversion.split('.')))[2] > self.getCurrentPgVer()[2]:
                pgi.envfile = 'env_pg_' + self.clustername + '.sh'
                if pgi.updateEnvFile(pgi.envfile) == 0:
                        pgi.sshclient.execute('source $HOME/env/' + pgi.envfile)
                pgi.startDB('stop')
                if pgi.startDB('start') == 0:
                    if not self.preinstsoft:
                        pgi.updatePgContribs('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion)
                    pgi.ldif2LDAP = {}
                    pgi.registerPgClusterLDAP()
        elif ((tuple(map(int, self.pgversion.split('.')))[1] > self.getCurrentPgVer()[1]) and (tuple(map(int, self.pgversion.split('.')))[0] == self.getCurrentPgVer()[0])) or (tuple(map(int, self.pgversion.split('.')))[0] > self.getCurrentPgVer()[0]):
            if pgi.upgrade() == 0:
                pgi.ldif2LDAP = {}
                pgi.registerPgClusterLDAP()
        
        
#         pgi.updateonly = self.upgradeonly
#         if self.upgradeonly:
#             if pgi.preupgrade() == 0:
#                 pgi.ldif2LDAP = {}
#                 if pgi.upgrade() == 0:
#                     pgi.registerPgClusterLDAP()
#         else:
#             if pgi.preupgrade() == 0:
#                 pgi.ldif2LDAP = {}
#             
#             shlfrmldap = pgi.getObjectDetailFromLDAP('cn=shared_preload_libraries,cn=resource,cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
#             if not shlfrmldap is None:
#                 for dn, rattr in shlfrmldap:
#                     bcpsharedlib = ''.join(rattr['pgConfParamValue'])
#                     pgi.setObjectDetail2LDAP(dn, {'pgConfParamValue': "''"})
#             pgi.installPgContribs('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion)
#             shlfrmldap = pgi.getObjectDetailFromLDAP('cn=shared_preload_libraries,cn=resource,cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
#             if not shlfrmldap is None:
#                 for dn, rattr in shlfrmldap:
#                     bcpsharedlib = ''.join(rattr['pgConfParamValue'])                    
#                     pgi.setObjectDetail2LDAP(dn, {'pgConfParamValue': bcpsharedlib})
#             if pgi.upgrade() == 0:
#                 pgi.registerPgClusterLDAP()
        
        stdOut.write("Exiting PgCluster upgrade" + self.name + " at " + str(time.strftime('%H:%M:%S')) + '\n')
        
    def getCurrentPgVer(self):
        rtr = None
        verfrmldap = self.getObjectDetailFromLDAP('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if not verfrmldap is None: 
            for dn, rattr in verfrmldap:
                rtr = tuple(map(int, ''.join(rattr['pgVersCompat']).split('.')))
        return rtr
    

class ThreadDbSyncConfFiles(threading.Thread):
    clustername = ''
    hostname = ''
    cnflname = ''
    cnfltext = ''
    pgb = None

    def __init__(self, hostname, clustername, cnflname, cnfltext):
        self.clustername = clustername
        self.hostname = hostname
        self.cnflname = cnflname
        self.cnfltext = cnfltext
    
        threading.Thread.__init__(self)
        self.threadID = 5
        self.name = 'PgSyncConfFiles'
        self.counter = 5

    def run(self):
        stdOut.write('Выкладываем конфигурационный файл ' + self.cnflname + '...\n')
        pgi = PgSyncConfFiles(self.pgb, self.hostname, self.clustername, self.cnflname, self.cnfltext)
        if pgi.exitstatus == 0:
            stdOut.write("Конфигурационный файл " + self.cnflname + " успешно выложен\n")
        else:
            stdOut.write("Произошла ошибка при выгрузке файла " + self.cnflname + '\n')
    

class ThreadDbSchemaInstall(threading.Thread):
    clustername = ''
    hostname = ''
    dbname = ''
    schemaname = ''
    schemaowner = ''
    roletbls = ''
    rolencoding = ''
    rolesearchpath = ''
    pgb = None

    def __init__(self, hostname, clustername, dbname,  schemaname, schemaowner, roletbls, rolencoding, rolesearchpath):
        self.clustername = clustername
        self.hostname = hostname
        self.dbname = dbname
        self.schemaname = schemaname
        self.schemaowner = schemaowner
        self.roletbls = roletbls
        self.rolencoding = rolencoding
        self.rolesearchpath = rolesearchpath
    
        threading.Thread.__init__(self)
        self.threadID = 4
        self.name = 'PgSchemaInstall'
        self.counter = 4

    def run(self):
        stdOut.write("Создаем схему " + self.schemaname + " at database " + self.dbname + '\n')
        pgi = PgSchemaInstaller(self.pgb, self.hostname, self.clustername, self.dbname, self.schemaname, self.schemaowner, self.roletbls, self.rolencoding, self.rolesearchpath)
        pgi.createSchema()
        if pgi.exitstatus == 0:
            stdOut.write("Схема " + self.schemaname + " успешно создана\n")
        else:
            stdOut.write("Произошла ошибка при создании cхемы " + self.schemaname + '\n')
                
                
class ThreadPgDatabaseInstall(threading.Thread):
    clustername = ''
    hostname = ''
    pgb = None

    def __init__(self, hostname, clustername, dbname, dbencoding, dbtablespace, dbtemplate, pgnetservice):
        self.clustername = clustername
        self.hostname = hostname
        self.dbname = dbname
        self.dbencoding = dbencoding
        self.dbtablespace = dbtablespace
        self.dbtemplate = dbtemplate
        self.pgnetservice = pgnetservice
        
        threading.Thread.__init__(self)
        self.threadID = 3
        self.name = 'PgDatabaseInstall'
        self.counter = 3

    
    def run(self):
        stdOut.write("Создаем базу " + self.dbname + " at cluster " + self.clustername + '\n')
        pgi = PgDatabaseInstaller(self.pgb, self.hostname, self.clustername, self.dbname, self.dbencoding, self.dbtablespace, self.dbtemplate, self.pgnetservice)
        if pgi.exitstatus == 0:
            stdOut.write("База " + self.dbname + " успешно создана\n")
        else:
            stdOut.write("Произошла ошибка при создании базы " + self.dbname + '\n')
        

class ThreadPgBouncerInstall(threading.Thread):
    clustername = ''
    hostname = ''
    port = 0
    mode = ''
    regldaponly = False
    
    def __init__(self, hostname, port, clustername, mode, regldaponly):
        self.clustername = clustername
        self.hostname = hostname
        self.port = port
        self.mode = mode
        self.regldaponly = regldaponly

        threading.Thread.__init__(self)
        self.threadID = 1
        self.name = 'PgBouncerInstall'
        self.counter = 1
        
                         
    def run(self):
        stdOut.write("Starting install " + self.name + " at " + str(time.strftime('%H:%M:%S')) + '\n')
        pgi = PgBouncerInstaller(self.hostname, self.port, self.clustername, self.mode)
        if pgi.exitstatus == 0:
            if pgi.install(self.regldaponly) == 0:
                pgi.registerPgBouncerLDAP()
        stdOut.write("Exiting PgBouncer install" + self.name + " at " + str(time.strftime('%H:%M:%S')) + '\n')


class ThreadSysLogMessages(threading.Thread):
    clustername = ''
    tail = ''
    sshclient = None
    
    
    def __init__(self, clustername, tail):
        self.clustername = clustername
        self.tail = tail
        
        threading.Thread.__init__(self)
        self.threadID = 4
        self.name = 'SysLogMessages'
        self.counter = 4

    def run(self):
        self.sshclient = SSHConnector(SYSLOG_SERVER)        
        self.sshclient.execute('tail -' + self.tail + ' /logs/' + self.clustername + '/syslog.log', True, SysLog)
            
        
class SysLog():        
    bufferIO = gtk.TextBuffer()

    @staticmethod
    def write(message):
        SysLog.bufferIO.insert(SysLog.bufferIO.get_end_iter(),message)


class stdOut():
    bufferIO = gtk.TextBuffer()
    
    @staticmethod
    def write(message):
        stdOut.bufferIO.insert(stdOut.bufferIO.get_end_iter(),message)


class PgClusterInstaller():
    distrlink = 'http://XXXXXX.XXXXX.XXX'
    needpythonver = 2.7
    pgencoding = 'UTF8'
    pglocale = 'ru_RU.UTF8'
    ldif2LDAP = {}
    clustername = ''
    dbaHostName = ''
    dbaport = ''
    pgversion = ''
    pgwalsize = ''
    pgblocksize = ''
    pgwalblocksize = ''
    pgver = ''
    pgbase = '/u00/app/postgres'
    pgadminusers = {'ZZZZZZ':'XXXXXXXXXXX'}
    pgstatusers = {'XXXXXXXXXX': 'XXXXXXXXXXXXXX'}
    instsoftonly = False
    oldatadir = ''
    oldpghome = ''
    oldpgport = 5432

        
    def __init__(self, dbaHostName, port, clustername, pgversion, instsoftonly, clusterparams):
        self.ldap = ldap.initialize('ldap://' + ldap_host + ':' + ldap_port)
        self.instsoftonly = instsoftonly
        self.clustername = clustername
        self.dbaHostName = dbaHostName
        if port == '':
            self.dbaport = '5432'
        else:
            self.dbaport = port
        self.pgversion = pgversion
        self.pgver = '.'.join(pgversion.split('.')[:-1]) + '.x'
        self.pgwalsize = clusterparams['walsize']
        self.pgblocksize = clusterparams['blocksize']
        self.pgwalblocksize = clusterparams['walblocksize']
        self.sshclient = SSHConnector(dbaHostName)
        self.sshclient.execute('export LANGUAGE="en:en"')


    def install(self):
        rtr = 1001
        curpythonver = ''
        postgresql_compiler = ''
        
        self.sshclient.execute('mkdir -p ~/env')
        if not self.instsoftonly:
            self.sshclient.execute('mkdir -p ~/bin')
            self.sshclient.execute('mkdir -p ~/lib')
            self.sshclient.execute('mkdir -p ~/log')
        
        if 'stdb_' in self.clustername:
            envfile = 'stdb_env_pg_' + self.clustername.split('stdb_')[-1] + '.sh'
        else:
            envfile = 'env_pg_' + self.clustername + '.sh'
            
        if self.buildEnvFile(envfile) == 0:
            self.sshclient.execute('source $HOME/env/' + envfile)
            
        if not self.instsoftonly:
            self.sshclient.execute('mkdir -p $PGBASE')
            self.sshclient.execute('mkdir -p $PGLOGDIR/postgres')
            self.sshclient.execute('mkdir -p $PGLOGDIR/../arch')
            self.sshclient.execute('mkdir -p $PGLOGDIR/../stdbarch')
            self.sshclient.execute('mkdir -p $PGBASE/distr/PostgreSQL/$PGVERSION')
            self.sshclient.execute('mkdir -p $PGBASE/backup')
            self.sshclient.execute('mkdir -p $PGLOGDIR/backup')
    
            self.buildNagiosConf()
            self.uploadPgClusterTools()

        whichpython = self.sshclient.execute('which python 2>&1 | grep -v "/usr/bin/which: no"')
        pythonflags = '--prefix=$HOME --with-threads --enable-shared'                                                       
        if whichpython != '':
            try:
                curpythonver = re.search(r'([0-9]+\.[0-9]+\.[0-9]+)', self.sshclient.execute(whichpython + ' -V 2>&1')).groups()[0]
            except:
                curpythonver = '0.0.0'
            lastpythonver = self.getLastestObjectVer(self.distrlink + '/Python/' + str(self.needpythonver))
            if self.checkPythonVer(curpythonver, lastpythonver):
                self.installPython("$PGBASE/distr/Python", pythonflags)
        else:
            self.installPython("$PGBASE/distr/Python", pythonflags)    
#             distribute=self.sshclient.execute('lsb_release -is')
        if self.checkPackages() != 0:
            return rtr

        precomp = ''
        precomp += ' --with-wal-segsize=' + str(self.pgwalsize) if self.pgwalsize != '' else ''
        precomp += ' --with-blocksize=' + str(self.pgblocksize) if self.pgblocksize != '' else ''
        precomp += ' --with-wal-blocksize=' + str(self.pgwalblocksize) if self.pgwalblocksize != '' else ''
        postcomp = " CFLAGS=-I${HOME}/include LIBS='-lldap -llber -lrt'"
        postgresql_compiler = "--prefix=$PGHOME  --with-python --with-ldap --with-libxml --with-libxslt --with-ossp-uuid --with-openssl" + precomp + postcomp
#         postgresql_compiler = "--prefix=$PGHOME  --with-python --with-ldap --with-libxml --with-libxslt --with-openssl" + precomp + postcomp        
        if self.getInstallPostgres("$PGBASE/distr/PostgreSQL/" + self.pgversion + "/", postgresql_compiler) == 0:
            stdOut.write("\nCreate link\n")
            self.sshclient.execute('rm -r $HOME/bin/pg_config && ln -s $PGHOME/bin/pg_config $HOME/bin/pg_config')
        else:
            return rtr
        rtr = self.installPythonModules()
        if rtr == 0:
            if not self.instsoftonly:
                if self.initDbInstall() == 0:
                    if self.changePgConfig('$PGDATA/postgresql.conf') == 0:
                        rtr = self.registerConFilesDB(['pg_ldap,cn=database_conf'], [('$$PGCLUSTERNAME', self.clustername)], True)
                        rtr = self.registerConFilesDB(['pg_hba,cn=database_conf', 'pg_ident,cn=database_conf'], [('$$PGCLUSTERNAME', self.clustername)], False)
#                         rtr = self.registerConFilesDB(['pg_hba,cn=database_conf', 'pg_ident,cn=database_conf', 'postgresql,cn=database_conf', 'pg_ldap,cn=database_conf'], [('$$PGCLUSTERNAME', self.clustername)])
        return rtr


    def preupgrade(self):
        rtr = 1001
        curpythonver = ''
        postgresql_compiler = ''
        
        frmldap = self.getObjectDetailFromLDAP('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if not frmldap is None: 
            for dn, rattr in frmldap:
                self.oldatadir = ''.join(rattr['pgData'])
                self.oldpghome = ''.join(rattr['pgHome'])
        frmldap = self.getObjectDetailFromLDAP('cn=port,cn=auth,cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if not frmldap is None: 
            for dn, rattr in frmldap:
                self.oldpgport = ''.join(rattr['pgConfParamValue'])
                    
        envfile = 'env_pg_' + self.clustername + '.sh'
        if self.buildEnvFile(envfile) == 0:
            self.sshclient.execute('source $HOME/env/' + envfile)

        if not self.updateonly:
            self.buildNagiosConf()
            self.uploadPgClusterTools()
    
            whichpython = self.sshclient.execute('which python 2>&1 | grep -v "/usr/bin/which: no"')
            pythonflags = '--prefix=$HOME --with-threads --enable-shared'                                                       
            if whichpython != '':
                curpythonver = re.search(r'([0-9]+\.[0-9]+\.[0-9]+)', self.sshclient.execute(whichpython + ' -V 2>&1')).groups()[0]
                lastpythonver = self.getLastestObjectVer(self.distrlink + '/Python/' + str(self.needpythonver))
                if self.checkPythonVer(curpythonver, lastpythonver):
                    self.installPython("$PGBASE/distr/Python", pythonflags)
            else:
                self.installPython("$PGBASE/distr/Python", pythonflags)    
    
            precomp = ''
            precomp += ' --with-wal-segsize=' + str(self.pgwalsize) if self.pgwalsize != '' else ''
            precomp += ' --with-blocksize=' + str(self.pgblocksize) if self.pgblocksize != '' else ''
            precomp += ' --with-wal-blocksize=' + str(self.pgwalblocksize) if self.pgwalblocksize != '' else ''
            postcomp = " CFLAGS=-I${HOME}/include LIBS='-lldap -llber -lrt'"
            postgresql_compiler = "--prefix=$PGHOME  --with-python --with-ldap --with-libxml --with-libxslt --with-ossp-uuid --with-openssl" + precomp + postcomp
#             postgresql_compiler = "--prefix=$PGHOME  --with-python --with-ldap --with-libxml --with-libxslt --with-openssl" + precomp + postcomp        
            if self.getInstallPostgres("$PGBASE/distr/PostgreSQL/" + self.pgversion + "/", postgresql_compiler) == 0:
                stdOut.write("\nCreate link\n")
                self.sshclient.execute('rm -r $HOME/bin/pg_config && ln -s $PGHOME/bin/pg_config $HOME/bin/pg_config')
            else:
                return rtr
            rtr = self.installPythonModules()
        else:
            rtr = 0
        if rtr == 0:
            if self.initDbInstall(False) == 0:
                if self.changePgConfig('$PGDATA/postgresql.conf') == 0:
                    rtr = self.registerConFilesDB(['pg_ldap,cn=database_conf'], [('$$PGCLUSTERNAME', self.clustername)], True)
                    rtr = self.registerConFilesDB(['pg_hba,cn=database_conf', 'pg_ident,cn=database_conf'], [('$$PGCLUSTERNAME', self.clustername)], False)
        return rtr
        
        
    def upgrade(self):
        rtr = 1001
        
        frmldap = self.getObjectDetailFromLDAP('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if not frmldap is None: 
            for dn, rattr in frmldap:
                self.oldatadir = ''.join(rattr['pgData'])
                self.oldpghome = ''.join(rattr['pgHome'])
        frmldap = self.getObjectDetailFromLDAP('cn=port,cn=auth,cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if not frmldap is None: 
            for dn, rattr in frmldap:
                self.oldpgport = ''.join(rattr['pgConfParamValue'])
                    
        envfile = 'env_pg_' + self.clustername + '.sh'
        self.sshclient.execute('ls $HOME/env/' + envfile)
        if self.sshclient.exit_status != 0:
            if self.buildEnvFile(envfile) == 0:
                self.sshclient.execute('source $HOME/env/' + envfile)
        else:
            if self.updateEnvFilePGDATA(envfile) == 0:
                self.sshclient.execute('source $HOME/env/' + envfile)
        if self.initDbInstall(False) == 0:
            if self.changePgConfig('$PGDATA/postgresql.conf') == 0:
                self.registerConFilesDB(['pg_ldap,cn=database_conf'], [('$$PGCLUSTERNAME', self.clustername)], True)
                self.registerConFilesDB(['pg_hba,cn=database_conf', 'pg_ident,cn=database_conf'], [('$$PGCLUSTERNAME', self.clustername)], False)
        
        stdOut.write('\nНачинаем обновление кластера ' + self.clustername + '...\n')
        try:
            self.sshclient.execute('mkdir -p $HOME/upgrade && cd $HOME/upgrade')        
            stdOut.write('Начинаем обновление PGDATA из ' + self.oldatadir + '...\n')
            self.sshclient.execute('pg_upgrade -d ' + self.oldatadir + ' -D $PGDATA -b ' + self.oldpghome + '/bin -B $PGHOME/bin -p ' + str(self.oldpgport) + ' -P ' + str(self.dbaport) + ' -j 15', True)
            if self.sshclient.exit_status == 0:
                time.sleep(5)
                stdOut.write('Обновление PGDATA прошло успешно.\nЗапускаем базу данных\n')
                if self.startDB('start') != 0:
                    raise Exception('Cannot start database')
                dbadm = pgDatabaseAdm()
                dbadm.pgClusterName = self.clustername
                dbadm.dbaHostName = self.dbaHostName
                dbadm.dbaPort = self.dbaport
                stdOut.write('Начинаем обновление tablespace-ов кластера ' + self.clustername + '...\n')
                baseslist =  self.sshclient.execute('psql -tA -P pager=off -P recordsep="&&" -c "\l+"').split('&&')
                stdOut.write('Собираем данные о tablespace-ах для обновления объектов в базах...\n')
                dbases = map(lambda k,v: dict({k.split('|')[0]: tuple(v.split('|')[1:])}), baseslist, baseslist)
                tspaces = map(lambda x: tuple(x.split('|')), self.sshclient.execute('psql -tA -P pager=off -P recordsep="&&" -c "\db+"').split('&&'))
                objectsts = map(lambda k,v: dict({k.split('|')[0]: map(lambda x: tuple(x.split('|')), self.sshclient.execute('psql -tA -P pager=off -P recordsep="&&" -c "select ' + "'ALTER ' || objectname || ' ' || schemaname || '." + '\\"' + "' || tablename || '" + '\\"' + " SET TABLESPACE ' || tablespace || ';' " + ' as sqlcommand, tablespace from (select ' + "'TABLE'::name as objectname, schemaname, tablename, tablespace from pg_tables union select 'INDEX'" + '::name as objectname, schemaname, indexname, tablespace  from pg_indexes) t where not tablespace   in (' + "'pg_global','pg_default'" + ')" ' + v.split('|')[0]).split('&&'))}), baseslist, baseslist)
                for ts in tspaces:
                    if '/tablespaces/' in ts[2]:
                        stdOut.write('Начинаем обновление tablespace-а ' + ts[0] + '...\n')
                        dbadm.pgTablespaceFrom = ts[0]
                        dbadm.pgTablespaceTo = ts[0] + '_bak'
#                         dbadm.pgTablespaceComment = ts[5]     # Для версии < 9.5
                        dbadm.pgTablespaceComment = ts[6]     # Для версии 9.5
                        dbadm.pgRelatedCommand('rename_tablespace')
                        if dbadm.exit_status == 0:
                            dbadm.pgTablespace = ts[0]
                            dbadm.pgRelatedCommand('create_tablespace')
                            if dbadm.exit_status == 0:
                                if dbadm.pgTablespaceComment != '':
                                    dbadm.pgRelatedCommand('comment_tablespace')
                                for dbs in filter(lambda x: [i for i in x.values() if ts[0] in i], dbases):
                                    for db in dbs:
                                        dbadm.dbName = db 
                                        stdOut.write('Обновляем tablespace ' + ts[0] + ' в базе ' + dbadm.dbName + '...\n')
                                        dbadm.pgRelatedCommand('settbl_database')
                                for objs in filter(lambda x: [i for i in x.values() if filter(lambda z: len(z) == 2 and z[1] == ts[0], i)], objectsts):
                                    for db in objs:
                                        stdOut.write('Обновляем tablespace ' + ts[0] + ' для прочих объектов в базе ' + dbadm.dbName + '...\n')
                                        dbadm.sqlCommandFile = '/tmp/' + dbadm.dbName + '_' + ts[0] + '.sql'                                        
                                        try:
                                            f = open(dbadm.sqlCommandFile, 'w')
                                            f.write(''.join(map(lambda x: ''.join(x[0]), objs[db])))
                                            f.close()
                                        finally:
                                            self.sshclient.putfile(dbadm.sqlCommandFile, dbadm.sqlCommandFile)
                                            os.remove(dbadm.sqlCommandFile)
                                        if self.sshclient.exit_status == 0:
                                            dbadm.dbName = db
                                            dbadm.pgRelatedCommand('run_command')
                                if dbadm.exit_status == 0:
                                    dbadm.pgTablespace = ts[0] + '_bak'
                                    dbadm.pgRelatedCommand('drop_tablespace')
                                rtr = dbadm.exit_status
                        if rtr == 0:
                            stdOut.write('Обновление tablespace-а ' + ts[0] + ' прошло успешно.\n')
                        else:
                            stdOut.write('Обновление tablespace-а ' + ts[0] + ' завершилось с ошибкой.\n')
                stdOut.write('Обновление кластера ' + self.clustername + ' прошло успешно.\n')
                rtr = 0
            else:
                stdOut.write('Произошла ошбика при обновлении кластера. Просмотрите log-файл обновления.\n')
        except Exception, e:
            stdOut.write('Произошла ошбика при обновлении кластера. ' + str(e.message) + '\n')
        return rtr
    
    
    def replaceParamInStream(self, paramalias, parambody):
        rtr = parambody
        if paramalias == 'stdb_recovery':
            frmldap = self.getObjectDetailFromLDAP('cn=' + self.clustername[5:] + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
            if not frmldap is None: 
                for dn, rattr in frmldap:
                    rtr = parambody.replace('$$HOSTNAME', ''.join(self.getRealHostname(rattr['dbaHostName']))).replace('$$PGPORT', ''.join(rattr['dbaPort']))
        if paramalias[:10] == 'postgresql':
            rtr = self.ldif2LDAP['cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'][0][1] # + "\npgrbc.clustername='" + self.clustername + "'\npgrbc.realclustername='" + self.clustername + "'"
        return rtr
    
    
    def registerConFilesDB(self, tmplnames, replacer = [], withupload = True):
        rtr = 1001
        try:
            for tmplname in tmplnames:
                tmplfrmldap = self.getTemplateBodyFromLDAP(tmplname)
                if not tmplfrmldap is None:
                    for dn, rattr in tmplfrmldap:
                        tmplstr = self.replaceParamInStream(''.join(rattr['cn']), ''.join(rattr['pgbConfigSettings']))
                        for repold, repnew in replacer:
                            tmplstr = tmplstr.replace(repold, repnew)
                        self.ldif2LDAP['cn=' + ''.join(rattr['cn']) + ',cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] = [('pgbConfigSettings', tmplstr)]
                        if withupload:
                            stdOut.write('Пытаемся выложить файл ' + ''.join(rattr['pgContribName']) + ' в автоматическом режиме...\n')
                            self.sshclient.execute('echo "' + base64.b64encode(tmplstr) + '" | base64 -d > $PGDATA/' + ''.join(rattr['pgContribName']))
                            stdOut.write('Файл ' + ''.join(rattr['pgContribName']) + ' успешно выложен\n')
            rtr = 0
        except Exception, e:
            stdOut.write('Ошибка в формировании файла ' + ''.join(rattr['pgContribName']) + ' в автоматическом режиме\n' + str(e))
            rtr = 1015
        return rtr

    
    def initDbInstall(self, withTablespaces = True):
        rtr = 1001
        
        try:
            self.sshclient.execute('mkdir -p $PGDATA')
            self.sshclient.execute('test -f $PGDATA/postgresql.conf')
            if self.sshclient.exit_status == 0:
                stdOut.write("\nВ директории $PGDATA найдены уже существующая структура БД PostgreSQL \n")
                stdOut.write("Начальная инициализация структуры БД пропускается...\n")
            else:
                stdOut.write("\nИнициализация нового 'кластера' баз данных...\n")
                if ('.'.join(self.pgversion.split('.')[:-1]) >= 11): 
                    self.sshclient.execute('initdb -D $PGDATA --wal-segsize=32 --encoding=' + self.pgencoding + ' --locale=' + self.pglocale, True)
                else:
                    self.sshclient.execute('initdb -D $PGDATA --encoding=' + self.pgencoding + ' --locale=' + self.pglocale, True)
                if withTablespaces:
                    self.sshclient.execute('mkdir -p $PGDATA/tablespaces/temp && chmod 700 $PGDATA/tablespaces/temp')
                rtr = self.sshclient.exit_status
        except:
            pass
        return rtr
    
        
    def changePgConfig(self, confile):
        rtr = 1001
        pgconfilebody = ''
        
        try:
            stdOut.write("\nПытаемся загрузить исходный файл конфигурации БД PostgreSQL...\n")
            
            pgconfilebody = '\n'.join(base64.b64decode(self.sshclient.execute('cat ' + confile + ' | base64')).split('\n'))
            if pgconfilebody != '':                
                stdOut.write("\nПытаемся применить шаблоны автоматической конфигурации БД PostgreSQL...\n")
        
                pgconfrmldap = self.getTemplateBodyFromLDAP('postgresql,cn=database_conf')
                if not pgconfrmldap is None: 
                    for dn, rattr in pgconfrmldap:
                        for sattr in ''.join(rattr['pgbConfigSettings']).split('\n'):
                            for rpar, vals in [filter(lambda x: len(x) > 0, sattr.split('\t'))]:
                                if '$' in vals:
                                    vals = self.sshclient.execute('echo "' + vals + '"')
                                pgconfilebody = self.pgParameterSet(pgconfilebody, rpar, vals)
        
                else:
                    stdOut.write("\nНевозможно получить шаблон изменений файла конфигурации PostgreSQLя \n")
                    stdOut.write(" версии " + self.pgversion + " для применения изменений...\n\n")
                    stdOut.write(" Автоматическое изенение конфигурации БД PostgreSQL отменяется...\n")
                    stdOut.write(" Проделайте эту операцию вручную...\n")
                    
                pgconfilebody = self.pgParameterSet(pgconfilebody, "port", self.dbaport)
                    
                self.ldif2LDAP['cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] = [('pgbConfigSettings', pgconfilebody)]
                rtr = 0
        except Exception, e:
            stdOut.write('Ошибка в обработке параметров БД...\n' + str(e))
        return rtr
        
        
    def pgParameterSet(self, pgconfig, pars, vals):
        rtr = pgconfig
        try:
            stdOut.write("Изменение параметра: " + pars + " -> " + vals + '\n')
            rtr = re.sub(r'[# \t]*(' + pars + '[ \t]*=[ \t]*)[^#\n]*(.*)','\g<1>' + vals + ' \g<2> # CHANGE AUTOMATTICALY',pgconfig)
                    
#            vval = self.sshclient.execute('echo "' + vals + '" | sed "' + "s/\\//\\\\\\\\\\//g" + '"')
    
#            self.sshclient.execute('sed "s/[# \\t]*\(' + pars + '[ \\t]*=[ \\t]*\)[^#]*\(.*\)/\\1 ' + vval + ' \\2 # CHANGE AUTOMATTICALY/" $PGDATA/' + pgconfig + ' > $PGDATA/' + pgconfig + '.tmp.' + pars)
#            self.sshclient.execute('cp $PGDATA/' + pgconfig + '.tmp.' + pars + ' $PGDATA/' + pgconfig)
#            self.sshclient.execute('rm $PGDATA/' + pgconfig + '.tmp.' + pars)
            
        finally:
            return rtr
        
        
    def getInstallPostgres(self, distr, flags):
        rtr = 1001
        stdOut.write('\n...Установка СУБД PostgreSQL...\n')
        try:
            self.sshclient.execute('mkdir -p ' + distr)
            self.sshclient.execute('cd ' + distr)
            stdOut.write('Скачиваем архив СУБД PostgreSQL из репозитория...\n')
            self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/PostgreSQL/DataBases/' + self.pgver + '/postgresql-' + self.pgversion + '.tar.gz')
            stdOut.write('Начинаем распаковку архива...\n')
            self.sshclient.execute('tar -zxf postgresql-' + self.pgversion + '.tar.gz')
            
            stdOut.write('\nНачинаем установку патчей...\n')
            rtr = self.getInstallPgPatches('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion, 'ldap_params')
            rtr = self.getInstallPgPatches('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion, 'ldap_resolve')
            rtr = self.getInstallPgPatches('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion, 'ldap_auth')
            if rtr != 0:
                stdOut.write('Установка патчей завершена с ошибкой...\n')
                return rtr
            else:
                stdOut.write('\nУстановка патчей завершена...\n')
                rtr = 1001
            
            if self.CompileSource('$PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion, flags, 'PostgreSQL DataBase v. ' + self.pgversion) != 0:
                stdOut.write('Установка завершена с ошибкой...\n')
                return rtr
            rtr = 0
        finally:
            return rtr
        
        
    def checkPackages(self):
        rtr = 1001
        packages = ''
        try:
            pkglstfrmldap = self.getTemplateBodyFromLDAP('package_list')
            if not pkglstfrmldap is None: 
                for dn, rattr in pkglstfrmldap:
                    self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings'])) + '" | base64 -d > $HOME/package_list.txt')
#                 if (distribute == "RedHatEnterpriseServer" ) or ( distribute == "SUSE LINUX") or ( distribute == "Ubuntu") or (distribute == "CentOS"):
                packages = self.sshclient.execute('cat $HOME/package_list.txt | sed -e"s/#.*$//"  | xargs rpm -qv | grep "is not installed" | awk ' + "'{print $2}'" +' | xargs')
                self.sshclient.execute('rm $HOME/package_list.txt')
                if packages != '':
                    stdOut.write(" Необходима установка дополнительно следующих пакетов:\n " + packages + "\n")
                    return
                rtr = 0
        finally:
            return rtr


    def getInstallPgPatches(self, distr, patchname):
        rtr = 0
        stdOut.write("Пытаемся найти подходящие файлы для патча " + patchname + " для PostgreSQL... \n")
        try:
            patchfile = 'patch_' + patchname + '_' + self.pgversion + '.patch'
            if self.sshclient.execute('wget --no-proxy --spider -q ' + self.distrlink + '/PostgreSQL/DataBases/Patches/' + patchname + '/' + patchfile + '; echo $?') != '0':
                patchfile = 'patch_' + patchname + '_' + self.pgver + '.patch'
                if self.sshclient.execute('wget --no-proxy --spider -q ' + self.distrlink + '/PostgreSQL/DataBases/Patches/' + patchname + '/' + patchfile + '; echo $?') != '0':
                    patchfile = 'patch_' + patchname + '.patch'
                    if self.sshclient.execute('wget --no-proxy --spider -q ' + self.distrlink + '/PostgreSQL/DataBases/Patches/' + patchname + '/' + patchfile + '; echo $?') != '0':
                        stdOut.write("\n Не удалось найти у применить патча " + patchname + " для PostgreSQL... \n")
                        stdOut.write(" Компиляция продолжиться без применения патча...\n\n")
                        return 1001
            self.sshclient.execute('cd ' + distr)
            self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/PostgreSQL/DataBases/Patches/' + patchname + '/' + patchfile)
#             if patchfile == 'patch_ldap_params_9.3.x.patch':
#                 self.sshclient.execute('patch -p1 < ' + distr + '/' + patchfile)
#             else:
            self.sshclient.execute('patch -f -p0 < ' + distr + '/' + patchfile)
            if self.sshclient.exit_status == 0:
                stdOut.write("Патч " + patchname + " успешно применен \n")
            else:
                stdOut.write("Патч " + patchname + " найден, но не применен из-за непредвиденной ошибки ((( \n")
            rtr = self.sshclient.exit_status
        except:
            rtr = 1005
        return rtr
        
        
    def buildNagiosConf(self):
        rtr = 1001
        stdOut.write('Пытаемся создать nagios.conf для PgCluster-а...\n')
        try:
            envfrmldap = self.getTemplateBodyFromLDAP('pg_nagios')
            if not envfrmldap is None:
                for dn, rattr in envfrmldap:
                    if self.clustername[:5] == 'stdb_':
                        self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGPORT', self.dbaport).replace('$$STATE', 'standby')) + '" | base64 -d > $HOME/env/' + ''.join(rattr['pgContribName']))
                    else:
                        self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGPORT', self.dbaport).replace('$$STATE', 'main')) + '" | base64 -d > $HOME/env/' + ''.join(rattr['pgContribName']))
            else:
                stdOut.write("\nСтандартных шаблонов для файла конфигурации nagios.conf не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")                
            rtr = 0 
        finally:
            return rtr
        
        
    def buildEnvFile(self, confdest):
        rtr = 1001
        stdOut.write("\nПытаемся получить шаблоны стандарного файла конфигурации для БД PostgreSQL...\n")
        try:
            envfrmldap = self.getTemplateBodyFromLDAP('env_pg_src')
            if not envfrmldap is None: 
                for dn, rattr in envfrmldap:
                    self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGBASE', self.pgbase).replace('$$PGVERSION', self.pgversion).replace('$$PGVER', self.pgver).replace('$$PGCLUSTERNAME', self.clustername)) + '" | base64 -d > ~/env/' + confdest)
                    stdOut.write("Применен стандартный шаблон для PostgreSQL\nфайла конфигурации " + confdest + "\n\n")
            else:
                stdOut.write("\nСтандартных шаблонов для файла конфигурации не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")
            rtr = 0
        finally:
            return rtr

    def updateEnvFile(self, confdest):
        rtr = 1001
        stdOut.write("\nИзменяем файла конфигурации для БД PostgreSQL...\n")
        try:
            envfrmldap = self.getTemplateBodyFromLDAP('env_pg_src')
            if not envfrmldap is None: 
                for dn, rattr in envfrmldap:
                    self.sshclient.execute('NEWPGHOME=`echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGBASE', self.pgbase).replace('$$PGVERSION', self.pgversion).replace('$$PGVER', self.pgver).replace('$$PGCLUSTERNAME', self.clustername)) + '" | base64 -d | grep "PGHOME="`;sed -i "s#PGHOME=.*#$NEWPGHOME#" ~/env/' + confdest)
                    stdOut.write("Применен стандартный шаблон для PostgreSQL\nфайла конфигурации " + confdest + "\n\n")
            else:
                stdOut.write("\nСтандартных шаблонов для файла конфигурации не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")
            rtr = 0
        finally:
            return rtr

    def updateEnvFilePGDATA(self, confdest):
        rtr = 1001
        stdOut.write("\nИзменяем файла конфигурации для БД PostgreSQL...\n")
        try:
            envfrmldap = self.getTemplateBodyFromLDAP('env_pg_src')
            if not envfrmldap is None: 
                for dn, rattr in envfrmldap:
                    self.sshclient.execute('NEWPGHOME=`echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGBASE', self.pgbase).replace('$$PGVERSION', self.pgversion).replace('$$PGVER', self.pgver).replace('$$PGCLUSTERNAME', self.clustername)) + '" | base64 -d | grep "PGHOME="`;sed -i "s#PGHOME=.*#$NEWPGHOME#" ~/env/' + confdest)
                    self.sshclient.execute('NEWPGDATA=`echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGBASE', self.pgbase).replace('$$PGVERSION', self.pgversion).replace('$$PGVER', self.pgver).replace('$$PGCLUSTERNAME', self.clustername)) + '" | base64 -d | grep "PGDATA="`;sed -i "s#PGDATA=.*#$NEWPGDATA#" ~/env/' + confdest)
                    stdOut.write("Применен стандартный шаблон для PostgreSQL\nфайла конфигурации " + confdest + "\n\n")
            else:
                stdOut.write("\nСтандартных шаблонов для файла конфигурации не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")
            rtr = 0
        finally:
            return rtr
        
    def checkPythonVer(self, curpythonver, lastpythonver):
        curver = re.search(r'([0-9]+)\.([0-9]+)\.([0-9]+)',curpythonver).groups()
        lastver = re.search(r'([0-9]+)\.([0-9]+)\.([0-9]+)',lastpythonver).groups()
        if tuple(map(int, (curver))) < tuple(map(int, (lastver))):
            return True
        else:
            return False
        
    def installPython(self, distrdir, flags):
        stdOut.write('...Установка языка Python...' + '\n\n')
        self.sshclient.execute('mkdir -p ' + distrdir)
        self.sshclient.execute('cd ' + distrdir)
        lastpythonver = self.getLastestObjectVer(self.distrlink + '/Python/' + str(self.needpythonver))
        self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/Python/' + str(self.needpythonver) + '/Python-' + lastpythonver + '.tgz')
        if self.sshclient.exit_status == 0:
            stdOut.write("Python-" + lastpythonver + "\n")
            self.sshclient.execute('tar -zxf Python-' + lastpythonver + '.tgz', True)
            self.CompileSource(distrdir + '/Python-' + lastpythonver, flags, "Python v. " + lastpythonver)
        else:
            stdOut.write("Невозможно загрузить исходники Python v." + lastpythonver + '\n')
        
    def installPythonModules(self):
        rtr = 1001
        stdOut.write("Начинаем установку дополнительных модулей Python...\n")
        try:
            modfrmldap = self.getTemplateBodyFromLDAP('python_modules')
            if not modfrmldap is None: 
                dn, rattr = modfrmldap[0]
                for mod in ''.join(rattr['pgbConfigSettings']).split():
                    rtr = self.installPythonModule(mod, "$PGBASE/distr/")
        finally:
            return rtr
        
    def installPythonModule(self, module, distrdir):
        rtr = 1001
        stdOut.write("Начинаем установку дополнительного модуля " + module + "...\n")
        self.sshclient.execute('mkdir -p ' + distrdir)
        self.sshclient.execute('cd ' + distrdir)
        try:
            self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/Python/Modules/' + module + '.tar.gz')
            if self.sshclient.exit_status == 0:
                self.sshclient.execute('tar -zxf ' + module + '.tar.gz', True)
                self.sshclient.execute('cd ' + module + '; python setup.py build && python setup.py install', True)
                rtr = self.sshclient.exit_status
                if rtr == 0:
                    stdOut.write("Модуль " + module + " успешно установлен.\n")
                else:
                    raise Exception("Ошибка компиляции или установки модуля " + module + "\n")
        except Exception, e:
            stdOut.write("Модуль " + module + " не установлен.\n" + str(e) + '\n')
        finally:
            return rtr
        
    def CompileSource(self, distrdir, flags, description):
        stdOut.write("Start compiling source...\n")
        stdOut.write("Source dir   ===>> " + distrdir + '\n')
        stdOut.write("Source flags ===>> " + flags + '\n')
        stdOut.write("Source name  ===>> " + description + '\n')
        self.sshclient.execute('cd ' + distrdir)
        self.sshclient.execute('./configure ' + flags, True) 
        if self.sshclient.exit_status != 0:
            stdOut.write('Error at configure of ' + description + '...\n')
            return 1001
        stdOut.write('Configure ' + description + ' SUSCESSFULLY...' + '\n\n' + ' Start of make it...' + '\n')
        self.sshclient.execute('gmake clean', True)
        self.sshclient.execute('gmake', True)
        if self.sshclient.exit_status != 0:
            stdOut.write('Error at compiling ' + description + '...\n')
            return 1001
        stdOut.write('Compiling ' + description + ' SUSCESSFULLY...' + '\n\n' + 'Start install it...\n')
        self.sshclient.execute('gmake install', True)
        if self.sshclient.exit_status != 0:
            stdOut.write('Error at installing ' + description + '...\n')
            return 1001
        return 0
        
        
    def uploadPgClusterTools(self):
        self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/PostgreSQL/DataBases/Tools/pgcluster_tools.tgz -O $PGBASE/distr/pgcluster_tools.tgz')
        try:
            self.sshclient.execute('tar zxf $PGBASE/distr/pgcluster_tools.tgz -C ~/')
        finally:
            self.sshclient.execute('rm $PGBASE/distr/pgcluster_tools.tgz')
    
    
    def getTemplateBodyFromLDAP(self, templtype):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + templtype + ',cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['pgbConfigSettings', 'pgContribName', 'cn'])
            
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def getObjectDetailFromLDAP(self, cncontext):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s(cncontext,ldap.SCOPE_BASE,'(cn=*)')
            
        except Exception, e:
            stdOut.write('Ошибка чтения детализации объекта в LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def setObjectDetail2LDAP(self, dn, param):
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgregcontrib', 'uid=pgregcontrib,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            try:
                for par in param.items():
                    self.ldap.modify_s(dn, [(ldap.MOD_REPLACE, par[0], par[1])]) 
            except Exception, e:
                stdOut.write(str(e) + '\n')
        except Exception, e:
            stdOut.write('Ошибка чтения детализации объекта в LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
            

    def checkStandby2LDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=stdb_recovery,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['cn'])
        except:
            stdOut.write('Не найдена запись в LDAP для cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr
            

    def check2LDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['cn'])
        except:
            stdOut.write('Не найдена запись в LDAP для cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def prepareStandby2LDAP(self, dn, action = ''):
        if action == 'ADD':
            self.ldif2LDAP[dn] += [('cn', 'stdb_recovery'),
                                                  ('objectClass', ['rbcContainer', 'rbcPgConfigTemplate', 'top']),
                                                  ('pgContribName', 'recovery.conf')]
            
        elif action == 'MODIFY':
            self.ldif2LDAP[dn] = [(self.ldapModeModify('cn=stdb_recovery,cn=confiles,' + dn, 'pgbConfigSettings'), 'pgbConfigSettings', self.ldif2LDAP['cn=stdb_recovery,cn=confiles,' + dn][0][1])]


    def prepare2LDAP(self, dn, action = ''):
        if action == 'ADD':
            self.ldif2LDAP[dn] = [('cn' , self.clustername),
                            ('objectClass', ['rbcContainer', 'rbcPgCluster', 'top']),
                            ('dbaServiceType', 'PostgreSQL'),
                            ('dbaHostName', self.dbaHostName),
                            ('dbaPort', str(self.dbaport)),
                            ('pgUser', 'postgres'),
                            ('pgHome', self.sshclient.execute('echo $PGHOME')),
                            ('pgData', self.sshclient.execute('echo $PGDATA')),
                            ('pgVersCompat', self.pgversion)]
            self.ldif2LDAP['cn=skytools,' + dn] = [('cn', 'skytools'),
                                                   ('objectClass', ['rbcPgCluster','rbcContainer','top']),
                                                   ('dbaServiceType', 'skytools'),
                                                   ('pgData', self.sshclient.execute('echo $PGDATA')),
                                                   ('pgHome', self.sshclient.execute('echo $PGHOME')),
                                                   ('pgUser', 'postgres')]
            self.ldif2LDAP['cn=contribs,' + dn] = [('cn', 'contribs'),
                                                  ('objectClass', ['rbcContainer', 'rbcPgContribsContainer', 'rbcPgContribsList', 'top']),
                                                  ('pgDistrib', self.sshclient.execute('echo $PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion))]
            self.ldif2LDAP['cn=dbs,' + dn] = [('cn', 'dbs'),
                                                  ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=users,' + dn] = [('cn', 'users'),
                                                  ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=confiles,' + dn] = [('cn', 'confiles'),
                                                  ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=pg_hba,cn=confiles,' + dn] += [('cn', 'pg_hba'),
                                                  ('objectClass', ['rbcContainer', 'rbcPgConfigTemplate', 'top']),
                                                  ('pgContribName', 'pg_hba.conf')]
            self.ldif2LDAP['cn=pg_ident,cn=confiles,' + dn] += [('cn', 'pg_ident'),
                                                  ('objectClass', ['rbcContainer', 'rbcPgConfigTemplate', 'top']),
                                                  ('pgContribName', 'pg_ident.conf')]
            self.ldif2LDAP['cn=postgresql,cn=confiles,' + dn] += [('cn', 'postgresql'),
                                                  ('objectClass', ['rbcContainer', 'rbcPgConfigTemplate', 'top']),
                                                  ('pgContribName', 'postgresql.conf')]
            self.ldif2LDAP['cn=auth,cn=postgresql,cn=confiles,' + dn] = [('cn', 'auth'), ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=listen_addresses,cn=auth,cn=postgresql,cn=confiles,' + dn] = [('cn', 'listen_addresses'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('listen_addresses'))]
            self.ldif2LDAP['cn=max_connections,cn=auth,cn=postgresql,cn=confiles,' + dn] = [('cn', 'max_connections'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('max_connections'))]
            self.ldif2LDAP['cn=port,cn=auth,cn=postgresql,cn=confiles,' + dn] = [('cn', 'port'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', str(self.dbaport))]
            self.ldif2LDAP['cn=log,cn=postgresql,cn=confiles,' + dn] = [('cn', 'log'), ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=log_min_duration_statement,cn=log,cn=postgresql,cn=confiles,' + dn] = [('cn', 'log_min_duration_statement'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('log_min_duration_statement'))]
            self.ldif2LDAP['cn=resource,cn=postgresql,cn=confiles,' + dn] = [('cn', 'resource'), ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=maintenance_work_mem,cn=resource,cn=postgresql,cn=confiles,' + dn] = [('cn', 'maintenance_work_mem'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('maintenance_work_mem'))]
            self.ldif2LDAP['cn=max_prepared_transactions,cn=resource,cn=postgresql,cn=confiles,' + dn] = [('cn', 'max_prepared_transactions'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('max_prepared_transactions'))]
            self.ldif2LDAP['cn=shared_buffers,cn=resource,cn=postgresql,cn=confiles,' + dn] = [('cn', 'shared_buffers'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('shared_buffers'))]
            self.ldif2LDAP['cn=shared_preload_libraries,cn=resource,cn=postgresql,cn=confiles,' + dn] = [('cn', 'shared_preload_libraries'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('shared_preload_libraries'))]
            self.ldif2LDAP['cn=temp_buffers,cn=resource,cn=postgresql,cn=confiles,' + dn] = [('cn', 'temp_buffers'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('temp_buffers'))]
            self.ldif2LDAP['cn=work_mem,cn=resource,cn=postgresql,cn=confiles,' + dn] = [('cn', 'work_mem'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('work_mem'))]
            self.ldif2LDAP['cn=wal,cn=postgresql,cn=confiles,' + dn] = [('cn', 'wal'), ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=archive_command,cn=wal,cn=postgresql,cn=confiles,' + dn] = [('cn', 'archive_command'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('archive_command'))]
            self.ldif2LDAP['cn=archive_mode,cn=wal,cn=postgresql,cn=confiles,' + dn] = [('cn', 'archive_mode'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('archive_mode'))]
            self.ldif2LDAP['cn=hot_standby,cn=wal,cn=postgresql,cn=confiles,' + dn] = [('cn', 'hot_standby'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('hot_standby'))]
            self.ldif2LDAP['cn=max_wal_senders,cn=wal,cn=postgresql,cn=confiles,' + dn] = [('cn', 'max_wal_senders'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('max_wal_senders'))]
            self.ldif2LDAP['cn=wal_keep_segments,cn=wal,cn=postgresql,cn=confiles,' + dn] = [('cn', 'wal_keep_segments'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('wal_keep_segments'))]
            self.ldif2LDAP['cn=wal_level,cn=wal,cn=postgresql,cn=confiles,' + dn] = [('cn', 'wal_level'), ('objectClass', ['rbcContainer', 'rbcPgPostgresqlConf', 'top']), ('pgConfParamValue', self.ldapParameterFromTemplate4DBLDAP('wal_level'))]
            
        elif action == 'MODIFY':
            self.ldif2LDAP[dn] = [(self.ldapModeModify(dn, 'dbaServiceType'), 'dbaServiceType', 'PostgreSQL'),
                                        (self.ldapModeModify(dn, 'dbaHostName'), 'dbaHostName', self.dbaHostName),
                                        (self.ldapModeModify(dn, 'dbaPort'), 'dbaPort', str(self.dbaport)),
                                        (self.ldapModeModify(dn, 'pgUser'), 'pgUser', 'postgres'),
                                        (self.ldapModeModify(dn, 'pgHome'), 'pgHome', self.sshclient.execute('echo $PGHOME')),
                                        (self.ldapModeModify(dn, 'pgData'), 'pgData', self.sshclient.execute('echo $PGDATA')),
                                        (self.ldapModeModify(dn, 'pgVersCompat'), 'pgVersCompat', self.pgversion)]
            self.ldif2LDAP['cn=contribs,' + dn] = [(self.ldapModeModify('cn=contribs,' + dn, 'pgDistrib'), 'pgDistrib', self.sshclient.execute('echo $PGBASE/distr/PostgreSQL/' + self.pgversion + '/postgresql-' + self.pgversion))]
#             self.ldif2LDAP['cn=pg_hba,cn=confiles,' + dn] = [(self.ldapModeModify('cn=pg_hba,cn=confiles,' + dn, 'pgbConfigSettings'), 'pgbConfigSettings', self.ldif2LDAP['cn=pg_hba,cn=confiles,' + dn][0][1])]
#             self.ldif2LDAP['cn=pg_ident,cn=confiles,' + dn] = [(self.ldapModeModify('cn=pg_ident,cn=confiles,' + dn, 'pgbConfigSettings'), 'pgbConfigSettings', self.ldif2LDAP['cn=pg_ident,cn=confiles,' + dn][0][1])]
#             self.ldif2LDAP['cn=postgresql_' + self.pgver + ',cn=confiles,' + dn] = [(self.ldapModeModify('cn=postgresql_' + self.pgver + ',cn=confiles,' + dn, 'pgbConfigSettings'), 'pgbConfigSettings', self.ldif2LDAP['cn=postgresql_' + self.pgver + ',cn=confiles,' + dn][0][1])]


    def update2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgadmin', 'uid=pgadmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in self.ldif2LDAP:
                    self.ldap.modify_s(rldif, self.ldif2LDAP[rldif]) 
            except Exception, e:
                stdOut.write('ERROR: ' + str(e) + '\nUpdate to LDAP dn: ' + str(rldif) + '\nLDIF: ' + str(self.ldif2LDAP[rldif]) + '\nlogin: ' + str(login) + ' passw: ' + str(passw[:1]) + '****' + str(passw[-1:]) + '\n')
            finally:
                self.ldap.bind_s('','')


    def add2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgadmin', 'uid=pgadmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in sorted(self.ldif2LDAP, key=lambda key: len(key.split('cn='))): 
                    try:
                        self.ldap.add_s(rldif, self.ldif2LDAP[rldif]) 
                    except Exception, e:
                        stdOut.write('ERROR: ' + str(e) + '\nAdd to LDAP dn: ' + str(rldif) + '\nLDIF: ' + str(self.ldif2LDAP[rldif]) + '\nlogin: ' + str(login) + ' passw: ' + str(passw[:1]) + '****' + str(passw[-1:]) + '\n')
            finally:
                self.ldap.bind_s('','')


    def ldapModeModify(self, dn, fltr):
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            rattr = self.ldap.search_s(dn, ldap.SCOPE_BASE,'(cn=*)', [fltr])
            for dn, attr in rattr:
                if attr == {}:
                    rtr =  ldap.MOD_ADD
                else:
                    rtr = ldap.MOD_REPLACE
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return rtr
    
    
    def ldapParameterFromTemplate(self, paramname):
        rtr = "''"
        pgconfrmldap = self.getTemplateBodyFromLDAP('postgresql,cn=database_conf')
        if not pgconfrmldap is None: 
            for dn, rattr in pgconfrmldap:
                for sattr in ''.join(rattr['pgbConfigSettings']).split('\n'):
                    for rpar, vals in [filter(lambda x: len(x) > 0, sattr.split('\t'))]:
                        if rpar == paramname:
                            rtr = vals
                            return rtr
        return rtr


    def ldapParameterFromTemplate4DBLDAP(self, paramname):
        rtr = "''"
        pgconfrmldap = self.getTemplateBodyFromLDAP('database_ldap_conf,cn=database_conf')
        if not pgconfrmldap is None: 
            for dn, rattr in pgconfrmldap:
                for sattr in ''.join(rattr['pgbConfigSettings']).split('\n'):
                    for rpar, vals in [filter(lambda x: len(x) > 0, sattr.split('\t'))]:
                        if rpar == paramname:
                            rtr = vals
                            return rtr
        return rtr
    

    def pgCreateTablespace(self, tsname, tscomment):
        if tscomment == '':
            tscomment = "Autogenerate tablespace at " + str(datetime.datetime.now())
        self.sshclient.execute('mkdir -p $PGDATA/tablespaces/' + tsname)
        self.sshclient.execute('chmod 700 $PGDATA/tablespaces/' + tsname)

        self.sshclient.execute('$PGHOME/bin/psql -p ' + self.dbaport + ' -c "CREATE TABLESPACE ' + tsname + " LOCATION '$PGDATA/tablespaces/" + tsname + "'" + '"')
        self.sshclient.execute('$PGHOME/bin/psql -p ' + self.dbaport + ' -c "COMMENT ON TABLESPACE ' + tsname + " IS '" + tscomment + "'" + '"')

        return


    def createTempTablespace(self):
        pgconfrmldap = self.getTemplateBodyFromLDAP('postgresql,cn=database_conf')
        if not pgconfrmldap is None: 
            for dn, rattr in pgconfrmldap:
                for sattr in ''.join(rattr['pgbConfigSettings']).split('\n'):
                    for rpar, vals in [filter(lambda x: len(x) > 0, sattr.split('\t'))]:
                        if rpar == 'temp_tablespaces':
                            self.pgCreateTablespace(vals.replace("'","").replace('"','').strip(), 'Temporary tablespace... Settings in postgresql.conf')
                            return


    def addAdminStatUsers(self):
        self.ldif2LDAP = {}
        for usr in self.pgadminusers:
            self.sshclient.execute('$PGHOME/bin/psql -p ' + self.dbaport + ' -c "CREATE USER ' + usr + " ENCRYPTED PASSWORD '" + self.pgadminusers[usr] + "' SUPERUSER INHERIT NOCREATEDB NOCREATEROLE NOREPLICATION" + '"')
            if self.sshclient.exit_status == 0:
                self.prepareAliasAdd2LDAP('cn=' + usr + ',cn=users,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', usr, 'uid=' + usr + ',ou=Users,dc=rbc,dc=ru')                
            self.add2LDAP()
        for usr in self.pgstatusers:
            self.sshclient.execute('$PGHOME/bin/psql -p ' + self.dbaport + ' -c "CREATE USER ' + usr + " ENCRYPTED PASSWORD '" + self.pgstatusers[usr] + "' NOSUPERUSER INHERIT NOCREATEDB NOCREATEROLE NOREPLICATION" + '"')
            if self.sshclient.exit_status == 0:
                self.prepareAliasAdd2LDAP('cn=' + usr + ',cn=users,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', usr, 'uid=' + usr + ',ou=Users,dc=rbc,dc=ru')                
            self.add2LDAP()
        
        
    def prepareAliasAdd2LDAP(self, dn, aliasname, aliasdn):
        self.ldif2LDAP[dn] = [('cn' , aliasname),
                            ('objectClass', ['top', 'alias', 'extensibleObject']),
                            ('aliasedObjectName', aliasdn)]


    def registerPgClusterAsStandby(self):
        rtr = 1001
        self.ldif2LDAP = {}
        stdOut.write('Вносим изменения о Standby Pg кластере в LDAP\n')
        try:
            self.registerConFilesDB(['stdb_recovery,cn=database_conf'])
            if self.checkStandby2LDAP() == None:
                self.prepareStandby2LDAP('cn=stdb_recovery,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'ADD')
                self.add2LDAP()
            else:
                self.prepareStandby2LDAP('cn=stdb_recovery,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'MODIFY')
                self.update2LDAP()
            rtr = 0
        except Exception, e:
            stdOut.write('Ошбка внесения изменений в LDAP\n' + str(e) + '\n')
        return rtr
    
    
    def registerPgClusterLDAP(self):
        rtr = 1001
        stdOut.write('Вносим изменения о Pg кластере в LDAP\n')
        try:
#             self.ldif2LDAP['cn=pg_hba,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] = [('pgbConfigSettings', 'Null')]
#             self.ldif2LDAP['cn=pg_ident,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] = [('pgbConfigSettings', 'Null')]
#             self.ldif2LDAP['cn=postgresql_' + self.pgver +',cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] = [('pgbConfigSettings', 'Null')]
#            self.ldif2LDAP = {}
            if self.check2LDAP() == None:
                self.prepare2LDAP('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'ADD')
                self.add2LDAP()
            else:
                self.prepare2LDAP('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'MODIFY')
                self.update2LDAP()
            rtr = 0
        except Exception, e:
            stdOut.write('Ошбка внесения изменений в LDAP\n' + str(e) + '\n')
        return rtr


    def startDB(self, command):
        rtr = 1001
        try:
            pgb = pgClusterAdm()
            pgb.dbaHostName = self.dbaHostName
            pgb.pgClusterName = self.clustername
            pgb.pgRelatedCommand(command)
            rtr = pgb.exit_status
        finally:
            return rtr


    def installPgContribs(self, distr):
        rtr = 1001
        contriberr = []
        contribok = []
        listcontribs = []

        stdOut.write("\nПытаемся найти и скомпилить contrib'ы по заранее подготовленному списку...\n")
        contribsfrmldap = self.getTemplateBodyFromLDAP('pg_contribs_' + self.pgver)
        if not contribsfrmldap is None:
            for dn, rattr in contribsfrmldap:
                listcontribs = ''.join(rattr['pgbConfigSettings']).split('\n')

        for contrib in listcontribs:
            if contrib.strip() != '':
                if  contrib[0] != ';':
                    try:
                        self.sshclient.execute('test -d ' + distr + '/contrib/' + contrib)
                        if self.sshclient.exit_status != 0:
    #                             if False:
                            if '{-}' == contrib.strip()[-3:]:
                                stdOut.write("\nДополнение " + contrib + " не требует скачивания, устанавливаем только EXTENSION\n")
                                stdOut.write("Начинаем установку дополнения " + contrib + "...\n")
                                rtr = self.setupPgContribs('extension', distr + '/contrib/', contrib.split('{')[0], contrib)
                            else:
                                stdOut.write("\nНеоригинальное дополнениe " + contrib + "\n")
                                stdOut.write("Скачиваем исходники дополнения " + contrib + "...\n")
                                self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/PostgreSQL/DataBases/Contribs/' + contrib.split('{')[0] + '.tar.gz -O ' + distr + '/contrib/' + contrib.split('{')[0] + '.tar.gz')
                                stdOut.write("Распаковываем дополнения " + contrib + "...\n")
                                self.sshclient.execute('tar zxf ' + distr + '/contrib/' + contrib.split('{')[0] + '.tar.gz -C ' + distr + '/contrib/')
                                if self.setupPgContribs('make', distr + '/contrib/', contrib.split('{')[0], contrib, self.instsoftonly) == 0:
                                    if not self.instsoftonly:
                                        if '{' in contrib:
                                            for cntrb in contrib.split('{')[1].split('}')[0].strip().split(','):
                                                if cntrb != "":
                                                    stdOut.write("\nНачинаем установку extension дополнения " + cntrb + "...\n")
                                                    rtr = self.setupPgContribs('extension', distr + '/contrib/', cntrb, contrib)
                                        else:
                                            stdOut.write("\nНачинаем установку extension дополнения " + contrib + "...\n")
                                            rtr = self.setupPgContribs('extension', distr + '/contrib/', contrib, contrib)
                                        
                        else:
                            stdOut.write("\nНачинаем установку дополнения " + contrib + "...\n")
                            rtr = self.setupPgContribs('install', distr + '/contrib/', contrib, contrib, self.instsoftonly)
                        if rtr == 0:
                            contribok.append(contrib)
                        else:
                            contriberr.append(contrib)
                    except Exception, e:
                        stdOut.write("Ошибка: " + str(e))
                        contriberr.append(contrib)
                rtr = 0
            else:
                stdOut.write("\nНевозможно получить список необходимы дополнений PostgreSQLя\n")
                stdOut.write("версии " + self.pgversion + " для их автоматического создания...\n")
                stdOut.write("\nАвтоматическое создание дополнений для БД PostgreSQL отменяется...\n")
                stdOut.write("Проделайте эту операцию вручную...\n")

        if contriberr != []:
            stdOut.write("\n========================================================\n")
            stdOut.write(" Список неустановленных дополнений к PostgreSQL:\n")
            stdOut.write(" " + ', '.join(contriberr) + "\n")
            stdOut.write("========================================================\n")
        if contribok != []:
            stdOut.write("\n========================================================\n")
            stdOut.write(" Список установленных дополнений к PostgreSQL:\n")
            stdOut.write(" " + ', '.join(contribok) + "\n")
            stdOut.write("========================================================\n")
        return rtr


    def updatePgContribs(self, distr):
        rtr = 1001
        contriberr = []
        contribok = []
        listcontribs = []

        stdOut.write("\nПытаемся обновить contrib'ы по заранее подготовленному списку...\n")
        contribsfrmldap = self.getObjectDetailFromLDAP('cn=contribs,cn=testdev,cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if not contribsfrmldap is None:
            for dn, rattr in contribsfrmldap:
                listcontribs = rattr['pgContribName']

        for contrib in listcontribs:
            if contrib.strip() != '':
                if  contrib[0] != ';':
                    try:
                        self.sshclient.execute('test -d ' + distr + '/contrib/' + contrib)
                        rtr = self.sshclient.exit_status
                        if rtr == 0:
                            if '{' in contrib:
                                for cntrb in contrib.split('{')[1].split('}')[0].strip().split(','):
                                    if cntrb != "":
                                        stdOut.write("\nНачинаем обновление extension дополнения " + cntrb + "...\n")
                                        rtr = self.setupPgContribs('extension', distr + '/contrib/', cntrb, contrib, True)
                            else:
                                stdOut.write("\nНачинаем обновление extension дополнения " + contrib + "...\n")
                                rtr = self.setupPgContribs('extension', distr + '/contrib/', contrib, contrib, True)
                        if rtr == 0:
                            contribok.append(contrib)
                        else:
                            contriberr.append(contrib)
                    except Exception, e:
                        stdOut.write("Ошибка: " + str(e))
                        contriberr.append(contrib)
                rtr = 0
            else:
                stdOut.write("\nНевозможно получить список необходимы дополнений PostgreSQLя\n")
                stdOut.write("версии " + self.pgversion + " для их автоматического создания...\n")
                stdOut.write("\nАвтоматическое создание дополнений для БД PostgreSQL отменяется...\n")
                stdOut.write("Проделайте эту операцию вручную...\n")

        if contriberr != []:
            stdOut.write("\n========================================================\n")
            stdOut.write(" Список необновленных дополнений к PostgreSQL:\n")
            stdOut.write(" " + ', '.join(contriberr) + "\n")
            stdOut.write("========================================================\n")
        if contribok != []:
            stdOut.write("\n========================================================\n")
            stdOut.write(" Список обновленных дополнений к PostgreSQL:\n")
            stdOut.write(" " + ', '.join(contribok) + "\n")
            stdOut.write("========================================================\n")
        return rtr


    def setupPgContribs(self, command, distr, contrib, realcontrib, reg2ldap = False):
        cgi = PgContribInstaller(self.dbaHostName, self.clustername, command, distr, contrib, realcontrib, reg2ldap)
        rtr = cgi.install()
        return rtr
        
    def getLastestObjectVer(self, objectname):
        rtr = ''
        r = urllib.urlopen(objectname + '/lastest.txt')
        rtr = r.readline().strip()
        return rtr
        
    def getRealHostname(self, clname):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + clname + ',cn=PgHosts,cn=PgConfig,dc=rbc,dc=ru',ldap.SCOPE_BASE,'(cn=*)',['dbaHostName'])
        except Exception, e:
            stdOut.write('Ошибка получения списка кластеров из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        if not attr is None: 
            for dn, rattr in attr:
                return ' '.join(rattr['dbaHostName'])
        else:
            return clname        
        
        
class PgContribInstaller():
    ldif2LDAP = {}
    dbaHostName = ''
    clustername = ''
    contribname = ''
    realcontribname = ''
    command = ''
    distr = ''
    pgport = 0
    restart = False
    pgbase = '/u00/app/postgres'
    updateonly = False
    
    def __init__(self, dbaHostName, clustername, command, distr, contribname, realcontribname, updateonly = False, restart = False):
        if not command in ('install','uninstall','make','extension'):
            stdOut.write('Команда ' + command + ' для установки contrib-ов не существует...\n')
            raise
        self.ldap = ldap.initialize('ldap://' + ldap_host + ':' + ldap_port)
        self.dbaHostName = dbaHostName
        self.clustername = clustername
        self.command = command
        self.distr = distr
        self.contribname = contribname
        self.realcontribname = realcontribname
        self.restart = restart
        self.sshclient = SSHConnector(dbaHostName)
        self.updateonly = updateonly
        self.pgversion = self.getPgVersionFromLDAP()
        if (not self.pgversion is None) and (self.pgversion != ''):
            self.pgvers = '.'.join(self.pgversion.split('.')[:-1]) + '.x'
        
        
    def install(self):
        rtr = 1001
        contribansfrmldap = None
        self.ldif2LDAP = {}
        
        if 'stdb_' in self.clustername:
            envfile = 'stdb_env_pg_' + self.clustername.split('stdb_')[-1] + '.sh'
        else:
            envfile = 'env_pg_' + self.clustername + '.sh'
        self.sshclient.execute('test -f $HOME/env/' + envfile)
        if self.sshclient.exit_status != 0:
            stdOut.write("\nPg-кластер " + self.clustername + " не установлен либо установлен некорректно...\n")
            stdOut.write("проверьте правильность заданных параметров и, при необходимости, перезапустите утилиту...\n")
            return rtr
        else:
            self.sshclient.execute('source $HOME/env/' + envfile)
        
        stdOut.write("Начинаем поиск...\n")
#             contribansfrmldap = self.checkEntryLDAP() 
#             if contribansfrmldap  == None:
#                 stdOut.write("\nНе удалось найти зарегистрированных записей о дополнениях \n")
#                 stdOut.write("к Pg-кластеру в регистрационном сервере LDAP.\n")
#                 stdOut.write("Проверьте правильность параметров и, в случае необходимости зарегистрируйте\n")
#                 stdOut.write("Переустановите Pg-кластер при помощи специальной утилиты")
#                 return rtr
                
        self.getPgPort()

        if self.distr == '':
            stdOut.write("\nНе найдена директория с дистрибутивом установленного Pg-кластера\n")
            stdOut.write("Проверьте правильность настроек или корректность информации регистрации\n")
            return rtr
        
        if self.command != "extension":
            self.sshclient.execute('test -d ' + self.distr + '/' + self.contribname)
            if self.sshclient.exit_status != 0:
                stdOut.write('\nВ директории дистрибутива Pg-кластера дополнения с именем ' + self.contribname + '  не найдено...\n')
                stdOut.write('Исправьте параметры запуска и повторите попытку выполнения программы...\n')
                return rtr
        
        if self.command == "install":
            rtr = self.pgContribInst(self.distr + '/' + self.contribname)
            if rtr == 0:
                if not self.updateonly:
                    self.prepare2LDAP('cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'ADD')
                    self.checkContribLDAP(self.contribname)
            else:
                return rtr
                    
        elif self.command == "make":
            rtr = self.contribMake(self.distr + '/' + self.contribname)
            if rtr == 0:
                if not self.updateonly:
                    self.prepare2LDAP('cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'ADD')
                    self.checkContribLDAP(self.contribname)
            else:
                return rtr

        elif self.command == "extension":
            rtr = self.InstallContribExtension()
            if rtr == 0:
                if not self.updateonly:
                    self.prepare2LDAP('cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'ADD')
            else:
                return rtr

        elif self.command == "uninstall":
            self.prepare2LDAP('cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'DEL')


        stdOut.write("\nНачинаем записывать информацию об установленных в кластере дополнениях в OiD(LDAP) сервер...\n")
        rtr = self.update2LDAP()
        if rtr != 0:
            stdOut.write("\nНе удалось записать изменения в OiD (LDAP) сервер...\n")
            stdOut.write("Попробуйте изменить нужные значения вручную...\n")
            return rtr
        
        stdOut.write("\n=============================================================\n")
        stdOut.write(" Установка дополнения " + self.contribname + " к Pg-кластеру " + self.clustername + "\n")
        stdOut.write("           прошла успешно........\n")
        stdOut.write("=============================================================\n\n")
        
        return rtr


    def update2LDAP(self):
        rtr = 0
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgregcontrib', 'uid=pgregcontrib,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in self.ldif2LDAP:
                    if len(self.ldif2LDAP[rldif]) == 1:
                        self.ldap.modify_s(rldif, self.ldif2LDAP[rldif]) 
                    else:
                        self.ldap.add_s(rldif, self.ldif2LDAP[rldif])
            except Exception, e:
                stdOut.write(str(e) + '\n')
                rtr = 1001
            finally:
                self.ldap.bind_s('','')
        return rtr


    def prepare2LDAP(self, dn, action = '', paramkv = {}):
        if action == 'DEL':
            self.ldif2LDAP[dn] = [(ldap.MOD_DELETE, 'pgContribName', [self.realcontribname])]
        else:
            if paramkv != {}:
                for k,v in paramkv.items():
                    relmod = self.ldapModeModify(dn, 'pgConfigSettings', k + '=' + v)
                    if not relmod is None:
                        self.ldif2LDAP[dn] = [(relmod, 'pgConfigSettings', [k + '=' + v])]
            else:
                relmod = self.ldapModeModify(dn, 'pgContribName', self.realcontribname)
                if not relmod is None:
                    self.ldif2LDAP[dn] = [(relmod, 'pgContribName', [self.realcontribname])]
    
    
    def ldapModeModify(self, dn, fltr, fltrval):
        rtr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            rattr = self.ldap.search_s(dn, ldap.SCOPE_BASE,'(cn=*)', [fltr])
            for dn, attr in rattr:
                if (attr == {}) or (not fltrval in attr[fltr]):
                    rtr =  ldap.MOD_ADD
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return rtr

    def InstallContribExtension(self):
        rtr = 1001
    
        stdOut.write("\nНачинаем устанавку EXTENSION дополнения PostgreSQL " + self.contribname + "...\n")
    
        self.sshclient.execute('test -f $PGHOME/share/extension/' + self.contribname + '.control')
        if self.sshclient.exit_status == 0:
            if self.updateonly:
                self.sshclient.execute('$PGHOME/bin/psql -p ' + str(self.pgport) + ' -c "CREATE EXTENSION IF NOT EXISTS ' + self.checkContribname4Install(self.contribname) + '; ALTER EXTENSION ' + self.checkContribname4Install(self.contribname) + ' UPDATE;" template1')
            else:
                self.sshclient.execute('$PGHOME/bin/psql -p ' + str(self.pgport) + ' -c "CREATE EXTENSION ' + self.checkContribname4Install(self.contribname) + ';" template1')
            if self.sshclient.exit_status == 0:
                rtr = self.pgContribSetvars()
        return rtr
        

    def contribMake(self, distrpath):
        rtr = 1001
        stdOut.write("\nНачинаем компиляцию дополнения PostgreSQL " + self.contribname + "...\n")
        rtr = self.CompileSource(distrpath)
        return rtr        


    def CompileSource(self, distrdir):
        rtr = 1001
        try:
            stdOut.write("Start compiling source...\n")
            stdOut.write("Source dir   ===>> " + distrdir + '\n')
            self.sshclient.execute('cd ' + distrdir)
            self.sshclient.execute('gmake clean && gmake', True)
            if self.sshclient.exit_status != 0:
                stdOut.write('Error at compiling ' + self.contribname + '...\n')
                rtr = 1002
            stdOut.write('Compiling SUSCESSFULLY...' + '\n\n' + 'Start install it...\n')
            self.sshclient.execute('gmake install', True)
            if self.sshclient.exit_status != 0:
                stdOut.write('Error at installing ' + self.contribname + '...\n')
                rtr = 1003
            rtr = 0 
        except:
            return rtr
        return rtr
        

    def getPgPort(self):
        port = self.getPostgreSQLParamsFromLDAP('port')
        if not port is None:
            for dn, attr in port:
                self.pgport = int(''.join(attr['pgConfParamValue']))
        else:
            self.pgport = 5432
#         self.sshclient.execute('test -f $PGDATA/postgresql.conf')
#         if self.sshclient.exit_status == 0:
#             port = self.sshclient.execute('cat $PGDATA/postgresql.conf | grep "[\\t ]*port[\\t ]*=[\\t ]*[0-9]\+" | sed "s/[\\t ]*port[\\t ]*=[\\t ]*\([0-9]\+\)[\\t #]*.*/\\1/"| grep -v "#"')
#             if port == '':
#                 port = 5432;
#             else:
#                 self.pgport = int(port)


    def pgContribInst(self, distr):
        rtr = 1001

        stdOut.write("\nНачинаем компиляцию и устанавку дополнения PostgreSQL " + self.contribname + "...\n")
    
        try:
            rtr = self.contribMake(distr)
            self.sshclient.execute('test -f $PGHOME/share/extension/' + self.contribname + '.control')
            if self.sshclient.exit_status == 0:
                if self.updateonly:
                    self.sshclient.execute('$PGHOME/bin/psql -p ' + str(self.pgport) + '  -c "CREATE EXTENSION IF NOT EXISTS ' + self.checkContribname4Install(self.contribname) + '; ALTER EXTENSION ' + self.checkContribname4Install(self.contribname) + ' UPDATE;" template1', True)
                else:
                    self.sshclient.execute('$PGHOME/bin/psql -p ' + str(self.pgport) + '  -c "CREATE EXTENSION ' + self.checkContribname4Install(self.contribname) + ';" template1', True)
                if self.sshclient.exit_status != 0:
                    return rtr
        except:
            return rtr
        rtr = 0
        return rtr
        
        
    def checkContribname4Install(self, contribname):
        if '-' in contribname:
            return '\\"' + contribname + '\\"'
        else:
            return contribname
        
        
    def pgContribSetvars(self):
        rtr = 1001
        confparams = ''
        
        stdOut.write("\nПроверяем наличие дополнительных параметров конфигураций для дополнения " + self.contribname + "...\n")

        confparams = self.getContribParams(self.contribname, self.pgvers)
        if confparams != '':
            for rpar in confparams.split('\n'):
                try:
                    paramname, paramval, sign = rpar.split(' ')
                except ValueError:
                    paramname, paramval = rpar.split(' ')
                    sign = ''
                
                if self.command == "install":
                    self.pgParameterSet("$PGDATA/postgresql.conf", paramname, paramval, sign)
                elif self.command == "uninstall":
                    if sign != '':
                        self.pgParameterSet("$PGDATA/postgresql.conf", paramname, paramval, '-')
                    else:
                        self.pgParameterDel("$PGDATA/postgresql.conf", paramname)
                
                rtr = 0
        else:
            stdOut.write("\nДополнение " + self.contribname + " не требует установки дополнительных конфигурационных параметров...\n")
            rtr = 0
        return rtr


    def pgParameterSet(self, pgconfile, paramname, paramval, sign):
        rtr = 1001

        vval = self.sshclient.execute('echo `eval "echo \"' + paramval + '\""`')
        stdOut.write("\nИзменение параметра: " + paramname + " -> " + paramval + "\n")
    
        if (sign == "*") or (sign == "+"):
            retparam = self.pgParameterGet(pgconfile, paramname)
            vval = self.sshclient.execute('`echo ' + retparam + ' | sed "' + "s/'\([^']*\)\(" + vval + "*\)\([^']*\)'\([^#]*\).*/'\\1\\3'\\4/" + '" |  sed "' + "s/'\([^']*\)'/'\\1," + vval + "'/" + '" | sed "' + "s/',/'/" + '"| sed "' + "s/,'/'/" + '" | sed "' + "s/,,/,/g" + '"`')
        elif (sign == "=") or (sign == "-"):
            retparam = self.pgParameterGet(pgconfile, paramname)
            vval = self.sshclient.execute('`echo ' + retparam + ' | sed "' + "s/'\([^']*\)" + vval + "\([^']*\)'\([^#]*\).*/'\\1\\2'\\3/" + '" | sed "' + "s/',/'/" + '" | sed "' + "s/,'/'/" + '" | sed "s/,,/,/g"`')
    
        vval = self.sshclient.execute('`echo ' + vval + ' | sed "s/\\//\\\\\\\\\\//g"`')
        self.sshclient.execute('sed "s/[# \\t]*\(' + paramname + '[ \\t]*=[ \\t]*\)[^#]*\(#\([^#]*\).*\)*/\\1 ' + vval + ' #\\3 #CHANGE AT $INSTCOMMAND contrib ' + self.contribname + '/" $PGDATA/' + pgconfile + ' > $PGDATA/' + pgconfile + '.tmp.' + paramname + '.$$')
        self.sshclient.execute('cp $PGDATA/' + pgconfile + '.tmp.' + paramname + '.$$ ' + pgconfile + ' && rm $PGDATA/' + pgconfile + '.tmp.' + paramname + '.$$')
        rtr = self.sshclient.execute('`cat $PGDATA/' + pgconfile + ' | grep -c "' + paramname + '"`')
        if rtr == 0:
            if (sign == "*") or (sign == "+"):
                self.sshclient.execute('echo -e "' + paramname + '=' + sign + ' # add at $INSTCOMMAND contrib ' + self.contribname + '">>$PGDATA/' + pgconfile)
        return rtr
            

    def pgParameterDel(self, pgconfile, paramname):
        rtr = 1001
    
        self.sshclient.execute('sed "s/\(^[ \\t]*$PARAM[ \\t]*=[ \\t]*\)/#\\1 /"  $PGDATA/' + pgconfile + ' >  $PGDATA/' + pgconfile + '.tmp.' + paramname + '.$$')
        self.sshclient.execute('cp $PGDATA/' + pgconfile + '.tmp.' + paramname + '.$$ ' + pgconfile + ' && rm $PGDATA/' + pgconfile + '.tmp.' + paramname + '.$$')
        rtr = 0
        return rtr


    def pgParameterGet(self, paramfile, paramname):
        return self.sshclient.execute('`cat ' + paramfile + ' | grep "' + paramname + '[ \\t]*=[ \\t]*" | sed "s/[# \\t]*' + paramname + '[ \\t]*=[ \\t]*\([^#]*\)\(.*\)/\\1/"`')


    def getContribParams(self, contribname, pgvers):
        rtr = ''
        cntrprmfrmldap = self.getContribParamsFromLDAP(contribname, pgvers)
        if not cntrprmfrmldap is None:
            for dn, rattr in cntrprmfrmldap:
                if ''.join(rattr['pgContribName']) == contribname:
                    rtr = ''.join(rattr['pgbConfigSettings'])
        return rtr
    

    def getPgVersionFromLDAP(self):
        attr = None
        rtr = ''
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'cn=*',['pgVersCompat'])
        except:
            stdOut.write('Не найдена запись в LDAP для cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        
        if not attr is None:
            for dn, rattr in attr:
                rtr = ''.join(rattr['pgVersCompat'])
        return rtr
        

    def getContribParamsFromLDAP(self, contribname, pgvers):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + contribname + ',cn=pg_contribs_' + pgvers + ',cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru', ldap.SCOPE_BASE,'cn=*',['pgContribName', 'pgbConfigSettings'])
        except:
            stdOut.write('Не найдена запись в LDAP для cn=' + contribname + ',cn=pg_contribs_' + pgvers + ',cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        

    def getPostgreSQLParamsFromLDAP(self, paramfltr):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_SUBTREE, '(&(cn=' + paramfltr + ')(objectClass=rbcPgPostgresqlConf))')
        except:
            stdOut.write('Не найдены записи конфигураций в LDAP для cn=postgresql,cn=confiles,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        
        

    def checkEntryLDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_ONELEVEL,'(&(cn=contribs)(objectClass=rbcPgContribsContainer))')
        except:
            stdOut.write('Не найдена запись в LDAP для cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def checkContribLDAP(self, contribname):
        try:
            attr = self.getContribParamsFromLDAP(contribname, self.pgvers)
            if not attr is None:
                for dn, rattr in attr:
                    for r in '\n'.join(rattr['pgbConfigSettings']).split('\n'):
                        if r.split(' ')[0].split('.')[0] == contribname:
                            if not 'cn=' + contribname + ',cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru' in  self.ldif2LDAP.keys():
                                self.ldif2LDAP['cn=' + contribname + ',cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] = [('cn', contribname),
                                                                                                                                                            ('objectClass', ['rbcContainer', 'rbcPgConfigTemplate', 'top']),
                                                                                                                                                            ('pgContribName', contribname)]
                                self.ldif2LDAP['cn=' + contribname + ',cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] += [('pgbConfigSettings', r.split(' ')[0].split('.')[1] + '=' + r.split(' ')[-1])]
                            else:
                                idx = 0
                                for par, parval in self.ldif2LDAP['cn=' + contribname + ',cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru']:
                                    if par == 'pgbConfigSettings':
                                        self.ldif2LDAP['cn=' + contribname + ',cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'][idx] = (par, parval + '\n' + r.split(' ')[0].split('.')[1] + '=' + r.split(' ')[-1])
                                        break
                                    idx += 1
                                if idx == len(self.ldif2LDAP['cn=' + contribname + ',cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru']):
                                    self.ldif2LDAP['cn=' + contribname + ',cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'] += [('pgbConfigSettings', r.split(' ')[0].split('.')[1] + '=' + r.split(' ')[-1])]
                        else:
                            attr_r = self.getPostgreSQLParamsFromLDAP(r.split(' ')[0])
                            if not attr_r is None:
                                for dn_r, rattr_r in attr_r:
                                    if not r.split(' ')[0].split('.')[0] in rattr_r['pgConfParamValue']:
                                        if ''.join(rattr_r['pgConfParamValue']) == "''" or ''.join(rattr_r['pgConfParamValue']) == '':
                                            self.ldif2LDAP[dn_r] = [(ldap.MOD_REPLACE, 'pgConfParamValue', "'" + contribname + "'")]
                                        else:
                                            self.ldif2LDAP[dn_r] = [(ldap.MOD_REPLACE, 'pgConfParamValue', "'" + ''.join(rattr_r['pgConfParamValue']).replace("'", "") + ',' + contribname + "'")]
        except Exception, e:
            stdOut.write('Не найдена запись в LDAP для cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru\n' + str(e) + '\n')
        

class PgSyncConfFiles():
    exitstatus = 0
    pgb = None
    clustername = ''
    hostname = ''
    cnflname = ''
    cnfltext = ''
    
    def __init__(self, pgb, hostname, clustername, cnflname, cnfltext):
        self.pgb = pgb
        self.clustername = clustername
        self.hostname = hostname
        self.cnflname = cnflname
        self.cnfltext = cnfltext
        
        self.exitstatus = self.syncFile()
        
    def syncFile(self):
        rtr = 1001
        self.pgb.pgClusterName = self.clustername
        self.pgb.dbaHostName = self.hostname
        self.pgb.ConfFileName = self.cnflname
        self.pgb.ConfFileText = base64.b64encode(self.cnfltext)
        
        stdOut.write('Пытаемся выгрузить файл ' + self.cnflname + '...\n')
        try:
            self.pgb.pgRelatedCommand('upload_conf_file')
            rtr = self.pgb.exit_status
        except:
            self.exitstatus = 1001
        return rtr


class PgSchemaInstaller():
    exitstatus = 0
    pgb = None
    ldif2LDAP = {}
    clustername = ''
    hostname = ''
    dbname = ''
    schemaname = ''
    schemaowner = ''
    roletbls = ''
    rolencoding = ''
    rolesearchpath = ''
    
    def __init__(self, pgb, hostname, clustername, dbname, schemaname, schemaowner, roletbls, rolencoding, rolesearchpath):
        self.ldap = ldap.initialize('ldap://' + ldap_host + ':' + ldap_port)
        self.pgb = pgb
        self.clustername = clustername
        self.hostname = hostname
        self.dbname = dbname
        self.schemaname = schemaname
        self.schemaowner = schemaowner
        self.roletbls = roletbls
        self.rolencoding = rolencoding
        self.rolesearchpath = rolesearchpath
        
        
    def createSchema(self):
        rtr = 1001
        self.pgb.pgClusterName = self.clustername
        self.pgb.dbaHostName = self.hostname
        self.pgb.dbName = self.dbname
        self.pgb.schemaName = self.schemaname
        self.pgb.schemaOwner = self.schemaowner
        self.pgb.dbEncoding = self.rolencoding
        self.pgb.pgTablespace = self.roletbls
        self.pgb.roleSearchPath = self.rolesearchpath
        
        stdOut.write('Пытаемся создать схему ' + self.schemaname + ' в базе ' + self.dbname + '...\n')
        try:
            stdOut.write('Пытаемся создать пользователя ' + self.schemaowner + '...\n')
            self.pgb.pgRelatedCommand('create_user')
            if self.pgb.exit_status == 0:
                if self.check2LDAP() == None:
                    self.prepare2LDAP('uid=' + self.schemaowner + ',ou=Users,dc=rbc,dc=ru', 'ADD')
                    self.add2LDAP()
                    stdOut.write('Пользователь ' + self.schemaowner + ' создан.\n')
                else:
                    stdOut.write('Пользователь ' + self.schemaowner + ' уже зарегистрирован в системе.\n')
                stdOut.write('Добавляем alias для пользователя ' + self.schemaowner + ' к базе ' + self.dbname + '...\n')
                self.ldif2LDAP = {}
                self.prepareAliasAdd2LDAP('cn=' + self.schemaowner + ',cn=users,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', self.schemaowner, 'uid=' + self.schemaowner + ',ou=Users,dc=rbc,dc=ru')                
                self.add2LDAP()                    
            self.pgb.pgRelatedCommand('create_schema')
            rtr = self.pgb.exit_status
        except Exception, e:
            stdOut.write('Ошибка при создании схемы\n' + str(e))
            self.exitstatus = 1001
        return rtr

    def createOnlyUser(self):
        rtr = 1001
        self.pgb.pgClusterName = self.clustername
        self.pgb.dbaHostName = self.hostname
        self.pgb.dbName = self.dbname
        self.pgb.schemaName = self.schemaname
        self.pgb.schemaOwner = self.schemaowner
        self.pgb.dbEncoding = self.rolencoding
        self.pgb.pgTablespace = self.roletbls
        self.pgb.roleSearchPath = self.rolesearchpath

        try:
            stdOut.write('Пытаемся создать пользователя ' + self.schemaowner + '...\n')
            self.pgb.pgRelatedCommand('create_user')
            if self.pgb.exit_status == 0:
                if self.check2LDAP() == None:
                    self.prepare2LDAP('uid=' + self.schemaowner + ',ou=Users,dc=rbc,dc=ru', 'ADD')
                    self.add2LDAP()
                    stdOut.write('Пользователь ' + self.schemaowner + ' создан.\n')
                else:
                    stdOut.write('Пользователь ' + self.schemaowner + ' уже зарегистрирован в системе.\n')
                stdOut.write('Добавляем alias для пользователя ' + self.schemaowner + ' к базе ' + self.dbname + '...\n')
                self.ldif2LDAP = {}
                self.prepareAliasAdd2LDAP('cn=' + self.schemaowner + ',cn=users,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', self.schemaowner, 'uid=' + self.schemaowner + ',ou=Users,dc=rbc,dc=ru')                
                self.add2LDAP()                    
        except Exception, e:
            stdOut.write('Ошибка при создании пользователя\n' + str(e))
            self.exitstatus = 1001
        return rtr
            
    def prepareAliasAdd2LDAP(self, dn, aliasname, aliasdn):
        self.ldif2LDAP[dn] = [('cn' , aliasname),
                            ('objectClass', ['top', 'alias', 'extensibleObject']),
                            ('aliasedObjectName', aliasdn)]

    def check2LDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('uid=' + self.schemaowner + ',ou=Users,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['cn'])
        except:
            stdOut.write('Не найдена запись в LDAP для uid=' + self.schemaowner + ',ou=Users,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr

    def prepare2LDAP(self, dn, action = ''):
        if action == 'ADD':
            self.ldif2LDAP[dn] = [('cn' , self.schemaowner),        
                    ('objectClass', ['inetOrgPerson', 'organizationalPerson', 'person']),
                            ('sn', self.schemaowner),
                            ('description', 'PostgreSQL Database user'),
                            ('employeeNumber', self.schemaowner),
                            ('givenName', self.schemaowner),
                            ('mail', 'asd@asdasd.asd'),
                            ('uid', self.schemaowner),
                            ('userPassword', self.getRolePasswd())]

    def add2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgadmin', 'uid=pgadmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in sorted(self.ldif2LDAP, key=lambda key: len(key.split('cn='))):
                    try: 
                        self.ldap.add_s(rldif, self.ldif2LDAP[rldif]) 
                    except Exception, e:
                        stdOut.write('ERROR: ' + str(e) + '\nAdd to LDAP dn: ' + str(rldif) + '\nLDIF: ' + str(self.ldif2LDAP[rldif]) + '\nlogin: ' + str(login) + ' passw: ' + str(passw[:1]) + '****' + str(passw[-1:]) + '\n')
            finally:
                self.ldap.bind_s('','')
    
    def getRolePasswd(self):
        passwd = ''.join(random.choice(string.ascii_lowercase + string.digits) for x in range(8))
        md5passw = md5.new(passwd)
        rtr = '{MD5}' + base64.b64encode(md5passw.digest())
        stdOut.write('Пароль для пользователя ' + self.schemaowner + ': ' +  passwd + '\n')
        return rtr
        

class PgDatabaseInstaller():
    exitstatus = 0
    pgb = None
    ldif2LDAP = {}
    clustername = ''
    hostname = ''
    dbname = ''
    dbencoding = 'UTF8'
    dbtablespace = 'pg_default'
    dbtemplate = 'template1'
    pgnetservice = ''
    
    def __init__(self, pgb, hostname, clustername, dbname, dbencoding, dbtablespace, dbtemplate, pgnetservice):
        self.ldap = ldap.initialize('ldap://' + ldap_host + ':' + ldap_port)
        self.pgb = pgb
        self.clustername = clustername
        self.hostname = hostname
        self.dbname = dbname
        if dbencoding != '':
            self.dbencoding = dbencoding
        if dbtablespace != '':
            self.dbtablespace = dbtablespace
        if dbtemplate != '':
            self.dbtemplate = dbtemplate
        self.pgnetservice = pgnetservice
        self.sshclient = SSHConnector(hostname)
        if self.createDatabase() == 0:
            self.exitstatus = self.registerDatabaseLDAP()
#             if self.registerDatabaseLDAP() == 0:
#                 self.exitstatus = self.registerDatabaseNagios() 
                
        
    def createDatabase(self):
        rtr = 1001
        self.pgb.pgClusterName = self.clustername
        self.pgb.dbaHostName = self.hostname
        self.pgb.dbName = self.dbname
        self.pgb.dbEncoding = self.dbencoding
        self.pgb.dbTemplate = self.dbtemplate
        self.pgb.pgTablespace = self.dbtablespace
        self.pgb.pgTablespaceComment = ''
        
        try:
            if self.dbtablespace != 'pg_default':
                stdOut.write('Пытаемся создать tablespace ' + self.dbtablespace + ' в базе ' + self.dbname + '...\n')
                self.pgb.pgRelatedCommand('create_tablespace')
                self.pgb.pgRelatedCommand('comment_tablespace')

            stdOut.write('Пытаемся создать базу данных ' + self.dbname + ' с параметрами:\ntablespace - ' + self.dbtablespace + '\nencoding - ' + self.dbencoding + '\ntemplate - ' + self.dbtemplate + '\nна кластере ' + self.clustername + '...\n')
            try:
                self.pgb.pgRelatedCommand('create_database')
                rtr = self.pgb.exit_status
            except:
                self.exitstatus = 1001
        except:
            self.exitstatus = 1001
        return rtr

    def check2LDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + self.dbname + ',cn=dbs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['cn'])
        except:
            stdOut.write('Не найдена запись в LDAP для cn=' + self.dbname + ',cn=dbs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def prepare2LDAP(self, dn, action = ''):
        if action == 'ADD':
            self.ldif2LDAP[dn] = [('cn' , self.dbname),        
                    ('objectClass', ['rbcPgDataBase', 'rbcPgContribsList', 'top']),
                            ('pgDBLocale', self.dbencoding),
                            ('pgDBOwner', 'postgres'),
                            ('pgDBTableSpace', self.dbtablespace),
                            ('pgDBGlobalID', str(self.getNextGlobalID()))]
#             self.ldif2LDAP['cn=contribs,' + dn] = [('cn', 'contribs'),
#                                                   ('objectClass', ['rbcContainer', 'rbcPgContribsContainer', 'rbcPgContribsList', 'top']),
#                                                   ('pgDistrib', self.getClusterPgDistrib(self.clustername)),
#                                                   ('pgContribName', self.getDbContribList(self.clustername))]
            if self.pgnetservice != '':
                self.ldif2LDAP['cn=' + self.pgnetservice + ',cn=PgNetServices,cn=PgContext,dc=rbc,dc=ru'] = [('cn' , self.pgnetservice),        
                        ('objectClass', ['rbcContainer', 'rbcPgNetService', 'top']),
                        ('dbaHostName', self.pgb.dbaHostName),
                        ('dbaPort', self.pgb.dbaPort),
                        ('pgConnectParams', 'host=' + self.pgb.dbaHostName + ' port=' + self.pgb.dbaPort + ' dbname=' + self.dbname),
                        ('pgDBName', self.dbname)]
        elif action == 'MODIFY':
            self.ldif2LDAP[dn] = [(self.ldapModeModify(dn, 'pgDBLocale'), 'pgDBLocale', self.dbencoding),
                                  (self.ldapModeModify(dn, 'pgDBOwner'), 'pgDBOwner', 'postgres'),
                                  (self.ldapModeModify(dn, 'pgDBTableSpace'), 'pgDBTableSpace', self.dbtablespace)]
                         
                         
    def ldapModeModify(self, dn, fltr):
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            rattr = self.ldap.search_s(dn, ldap.SCOPE_BASE,'(cn=*)', [fltr])
            for dn, attr in rattr:
                if attr == {}:
                    rtr =  ldap.MOD_ADD
                else:
                    rtr = ldap.MOD_REPLACE
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return rtr

    def update2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgregdbs', 'uid=pgregdbs,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in self.ldif2LDAP:
                    self.ldap.modify_s(rldif, self.ldif2LDAP[rldif]) 
            except Exception, e:
                stdOut.write(str(e) + '\n')
            finally:
                self.ldap.bind_s('','')


    def add2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgregdbs', 'uid=pgregdbs,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in sorted(self.ldif2LDAP, key=lambda key: len(key.split('cn='))): 
                    try:
                        self.ldap.add_s(rldif, self.ldif2LDAP[rldif]) 
                    except Exception, e:
                        stdOut.write('ERROR: ' + str(e) + '\nAdd to LDAP dn: ' + str(rldif) + '\nLDIF: ' + str(self.ldif2LDAP[rldif]) + '\nlogin: ' + str(login) + ' passw: ' + str(passw[:1]) + '****' + str(passw[-1:]) + '\n')
            finally:
                self.ldap.bind_s('','')
                                  
    def getNextGlobalID(self):
        maxid = 0
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            rattr = self.ldap.search_s('cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_SUBTREE,'(pgDBGlobalID=*)', ['pgDBGlobalID'])
            for dn, attr in rattr:
                if int(''.join(attr['pgDBGlobalID'])) > maxid:
                    maxid = int(''.join(attr['pgDBGlobalID']))
        except:
            stdOut.write('Не найден максимальный GlobalID в LDAP для ' + self.dbname + '\n')
        finally:
            self.ldap.bind_s('','')
        return maxid + 1

    def getClusterPgDistrib(self, clustername):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            rattr = self.ldap.search_s('cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(pgDistrib=*)', ['pgDistrib'])
            for dn, attr in rattr:
                break
        except:
            stdOut.write('Не найдена записи contribs в LDAP для кластера ' + self.clustername + '\n')
        finally:
            self.ldap.bind_s('','')
        if attr != None:
            return ''.join(attr['pgDistrib'])
        else:
            return ''
    
    def getDbContribList(self, clustername):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            rattr = self.ldap.search_s('cn=contribs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(pgContribName=*)', ['pgContribName'])
            for dn, attr in rattr:
                break
        except:
            stdOut.write('Не найдена записи contribs в LDAP для кластера ' + self.clustername + '\n')
        finally:
            self.ldap.bind_s('','')
        if attr != None:
            return attr['pgContribName']
        else:
            return []

    def registerDatabaseLDAP(self):
        rtr = 1001
        try:
            self.ldif2LDAP = {}
            if self.check2LDAP() == None:
                self.prepare2LDAP('cn=' + self.dbname + ',cn=dbs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'ADD')
                self.add2LDAP()
            else:
                self.prepare2LDAP('cn=' + self.dbname + ',cn=dbs,cn=' + self.clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'MODIFY')
                self.update2LDAP()
            rtr = 0
        except Exception, e:
            stdOut.write('Ошибка внесения изменений в LDAP\n' + str(e) + '\n')
        return rtr


    def registerDatabaseNagios(self):
        rtr = 1001
        try:
            envfrmldap = self.getConfFromLDAP('pg_nagios')
            if not envfrmldap is None:
                for dn, rattr in envfrmldap:
                    self.sshclient.execute("test -f $HOME/env/" + ''.join(rattr['pgContribName']))
                    if self.sshclient.exit_status == 0:
                        self.sshclient.execute("")
                
        except Exception, e:
            stdOut.write('Ошибка внесения изменений в nagios.conf\n' + str(e) + '\n')
        return rtr

        
    def getConfFromLDAP(self, confname):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + confname + ',cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', [])
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr


class PgBouncerInstaller():
    distrlink = 'XXXXXXX.XX.XX'
    needpythonver = 2.7
    ldif2LDAP = {}
    stbname = ''
    dbaHostName = ''
    dbaport = ''
    stbmode = ''
    exitstatus = 0
    pgbase = '/u00/app/postgres'
    
    def __init__(self, dbaHostName, port, stbname, stbmode):
        if (dbaHostName == '') or (port == '') or (stbname == '') or (stbmode == ''):
            stdOut.write('Не задан один из параметров для установки PgBouncer-a\n')
            self.exitstatus = 1001
            return
        self.ldap = ldap.initialize('ldap://' + ldap_host + ':' + ldap_port)
        self.stbname = stbname
        self.dbaHostName = dbaHostName
        self.dbaport = port
        self.stbmode = stbmode
        self.sshclient = SSHConnector(dbaHostName)
        self.sshclient.execute('export STBNAME=' + stbname) 
        self.sshclient.execute('export STBBASE=$HOME')
        self.sshclient.execute('export STBCONFDIR=$STBBASE/etc/pgbouncer')
        self.sshclient.execute('export STBLOGDIR=$STBBASE/log')
        self.sshclient.execute('export STBVARDIR=$STBBASE/var')
        self.sshclient.execute('export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$STBBASE/lib')
        self.sshclient.execute('export DISTRDIR=$HOME/distr')
        
    def __destroy__(self):
        self.ldap.bind_s('','')
        self.ldap = None
        
    def getStbVersion(self):
        res = 0
        res = self.sshclient.execute('$STBBASE/bin/pgbouncer -V')
        m = re.search(r'([0-9]\.[0-9]\.[0-9]$)', res)
        if m != None:
            res = m.group()
        else:
            res = self.getLastestObjectVer(self.distrlink + '/PostgreSQL/PgBouncer')
        return res
        
    def install(self, regldaponly):
        res = 1001
        curpythonver = ''
        
        self.sshclient.execute('mkdir -p $STBCONFDIR/$STBNAME')
        self.sshclient.execute('mkdir -p $STBLOGDIR')
        self.sshclient.execute('mkdir -p $STBVARDIR')
        self.sshclient.execute('mkdir -p $DISTRDIR')
        self.sshclient.execute('mkdir -p $HOME/env')

        if not regldaponly:
            whichpython = self.sshclient.execute('which $HOME/bin/python 2>&1 | grep -v "/usr/bin/which: no"')
            pythonflags = '--prefix=$HOME --with-threads --enable-shared'                                                       
            if whichpython != '' and not 'no python' in whichpython:
                curpythonver = self.sshclient.execute(whichpython + ' -V 2>&1')
                curpythonver = float(re.search(r'([0-9]+\.[0-9]+)', curpythonver).groups()[0])
                if curpythonver != self.needpythonver:
                    self.installPython("$DISTRDIR/Python", pythonflags)
            else:
                self.installPython("$DISTRDIR/Python", pythonflags)
               
            self.sshclient.execute('test -f $HOME/lib/libevent.so') 
            if self.sshclient.exit_status == 0:
                libeventver = float(self.sshclient.execute("ls -lah $HOME/lib/libevent.so | awk '{print $11}' | sed " + '"s/libevent-\([0-9.]\+\).so.*/\\1/"'))
            else:
                libeventver = 0
            lastlibeventver = float('.'.join(self.getLastestObjectVer(self.distrlink + '/Libs/libevent').split('.',2)[:2])) 
            if (libeventver == 0) or (libeventver != 0 and lastlibeventver != libeventver):
                libeventcompiler="--prefix=$HOME --enable-static --enable-shared"
                self.installLibEvent('$DISTRDIR/libs/libevent', libeventcompiler)
            bounflags="--prefix=$STBBASE --with-libevent=${HOME} --with-openssl --disable-debug LDFLAGS=-L${HOME}/lib CFLAGS=-I${HOME}/include LIBS='-lldap -llber'"
            res = self.installPgbouncer("$DISTRDIR/PgBouncer", bounflags)
        else:
            res = 0
        if res == 0:
            res = self.buildNagiosConf()
            if res == 0:
                res = self.buildEnvFile()
        return res

        
    def installPgbouncer(self, distrdir, flags):
        res = 1001
        stdOut.write('...Установка PgBouncer...\n\n')
        self.sshclient.execute('mkdir -p ' + distrdir)
        self.sshclient.execute('cd ' + distrdir)
        lastbounver = self.getLastestObjectVer(self.distrlink + '/PostgreSQL/PgBouncer')
        if lastbounver != 0:
            self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/PostgreSQL/PgBouncer/pgbouncer-' + lastbounver + '.tgz')
            if self.sshclient.exit_status == 0:
                stdOut.write("PgBouncer-" + lastbounver)
                self.sshclient.execute('tar -zxf pgbouncer-' + lastbounver + '.tgz', True)
                res = self.CompileSource(distrdir + '/pgbouncer-' + lastbounver, flags, "PgBouncer v. " + lastbounver)
            else:
                stdOut.write("Невозможно загрузить исходники PgBouncer v." + lastbounver + '\n')
        return res
    
        
    def installPython(self, distrdir, flags):
        stdOut.write('...Установка языка Python...' + '\n\n')
        self.sshclient.execute('mkdir -p ' + distrdir)
        self.sshclient.execute('cd ' + distrdir)
        lastpythonver = self.getLastestObjectVer(self.distrlink + '/Python/' + str(self.needpythonver))
        self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/Python/' + str(self.needpythonver) + '/Python-' + lastpythonver + '.tgz')
        if self.sshclient.exit_status == 0:
            stdOut.write("Python-" + lastpythonver + "\n")
            self.sshclient.execute('tar -zxf Python-' + lastpythonver + '.tgz', True)
            self.CompileSource(distrdir + '/Python-' + lastpythonver, flags, "Python v. " + lastpythonver)
        else:
            stdOut.write("Невозможно загрузить исходники Python v." + lastpythonver + '\n')
        
        
    def installLibEvent(self, distrdir, compiler):
        stdOut.write('\n'+"...Установка библиотеки libevent..."+'\n')
        self.sshclient.execute('mkdir -p ' + distrdir)
        self.sshclient.execute('cd ' + distrdir)
        lastlibeventver = self.getLastestObjectVer(self.distrlink + '/Libs/libevent')
        libeventdistr = 'libevent-' + lastlibeventver + '.tar.gz'
        self.sshclient.execute('wget --no-proxy -Nq ' + self.distrlink + '/Libs/libevent/' + libeventdistr)
        if self.sshclient.exit_status == 0:
            self.sshclient.execute('tar -zxf ' + libeventdistr, True)
            self.CompileSource(distrdir + '/libevent-' + lastlibeventver, compiler, 'LibEvent v. ' + lastlibeventver)
        else:
            stdOut.write('Невозможно загрузить исходники LibEvent v.' + lastlibeventver + '\n')
            return 1001
        
        
    def CompileSource(self, distrdir, flags, description):
        stdOut.write("Start compiling source...\n")
        stdOut.write("Source dir   ===>> " + distrdir + '\n')
        stdOut.write("Source flags ===>> " + flags + '\n')
        stdOut.write("Source name  ===>> " + description + '\n')
        self.sshclient.execute('cd ' + distrdir)
        self.sshclient.execute('./configure ' + flags, True)
        if self.sshclient.exit_status != 0:
            stdOut.write('Error at configure of ' + description + '...\n')
            return 1001
        stdOut.write('Configure ' + description + ' SUSCESSFULLY...' + '\n\n' + ' Start of make it...' + '\n')
        self.sshclient.execute('gmake clean', True)
        self.sshclient.execute('gmake', True)
        if self.sshclient.exit_status != 0:
            stdOut.write('Error at compiling ' + description + '...\n')
            return 1001
        stdOut.write('Compiling ' + description + ' SUSCESSFULLY...' + '\n\n' + 'Start install it...\n')
        self.sshclient.execute('gmake install', True)
        if self.sshclient.exit_status != 0:
            stdOut.write('Error at installing ' + description + '...\n')
            return 1001
        return 0
        
        
    def getLastestObjectVer(self, objectname):
        rtr = ''
        r = urllib.urlopen(objectname + '/lastest.txt')
        rtr = r.readline().strip()
#        rtr = '.'.join(rtr.split('.')[:2])
        return rtr
        

    def buildEnvFile(self):
        rtr = 1001
        stdOut.write("\nПытаемся получить шаблоны стандарного файла конфигурации для PgBouncer...\n")
        try:
            envfrmldap = self.getConfFromLDAP('stb_env_pg_src')
            if not envfrmldap is None: 
                for dn, rattr in envfrmldap:
                    self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGBASE', self.pgbase)) + '" | base64 -d > ~/env/' + ' '.join(rattr['pgContribName']))
                    stdOut.write("Применен стандартный шаблон для PgBouncer-a, файла конфигурации " + ' '.join(rattr['pgContribName']) + "\n\n")
            else:
                stdOut.write("\nСтандартных шаблонов для файла конфигурации не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")
            rtr = 0
        finally:
            return rtr

    
    def buildNagiosConf(self):
        rtr = 1001
        stdOut.write('Пытаемся создать или дополнить nagios.conf для новой конфигурации PgBouncer-а...\n')
        try:
            envfrmldap = self.getConfFromLDAP('stb_nagios')
            if not envfrmldap is None:
                for dn, rattr in envfrmldap:
                    self.sshclient.execute("test -f $HOME/env/" + ''.join(rattr['pgContribName']))
                    if self.sshclient.exit_status == 0:
                        self.sshclient.execute('cat $HOME/env/' + ''.join(rattr['pgContribName']) + '|grep -x port=' + self.dbaport)
                        if self.sshclient.exit_status != 0:
                            self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGPORT', self.dbaport)) + '" | base64 -d >> $HOME/env/' + ''.join(rattr['pgContribName']))
                    else:
                        self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings']).replace('$$PGPORT', self.dbaport)) + '" | base64 -d > $HOME/env/' + ''.join(rattr['pgContribName']))
            else:
                stdOut.write("\nСтандартных шаблонов для файла конфигурации nagios.conf не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")                
            rtr = 0 
        finally:
            return rtr
        
    
    def getConfFromLDAP(self, confname):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + confname + ',cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', [])
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        
    
    def check2LDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + self.stbname + ',cn=PgBouncers,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['cn'])
        except:
            stdOut.write('Не найдена запись в LDAP для cn=' + self.stbname + ',cn=PgBouncers,cn=PgContext,dc=rbc,dc=ru\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        
    def ldapModeModify(self, dn, fltr):
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            rattr = self.ldap.search_s(dn, ldap.SCOPE_BASE,'(cn=*)', [fltr])
            for dn, attr in rattr:
                if attr == {}:
                    rtr =  ldap.MOD_ADD
                else:
                    rtr = ldap.MOD_REPLACE
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return rtr
            
        
    def prepare2LDAP(self, dn, action = ''):
        if action == 'ADD':
            self.ldif2LDAP[dn] = [('cn' , self.stbname),
                            ('objectClass', ['rbcContainer', 'rbcPgBouncer', 'top']),
                            ('dbaServiceType', 'PgBouncer'),
                            ('dbaHostName', self.dbaHostName),
                            ('stdMode', self.stbmode),
                            ('dbaPort', str(self.dbaport)),
                            ('pgUser', 'postgres'),
                            ('dbaConfig', self.sshclient.execute('echo ${STBCONFDIR}/${STBNAME}/config_ldap.ini')),
                            ('pgbAdminUsers', 'ss'),
                            ('pgbConfigSettings', ['listen_addr =  *', 'listen_port = ' + str(self.dbaport), 
                            'unix_socket_dir = /tmp', 
                            'server_reset_query = RESET ALL; SET SESSION AUTHORIZATION DEFAULT; SET SESSION ROLE TO DEFAULT;', 
                            'ignore_startup_parameters = extra_float_digits, application_name', 
                            'server_check_query = SELECT 1', 
                            'server_check_delay = 10', 
                            'max_client_conn = 500', 
                            'default_pool_size = 50', 
                            'reserve_pool_size = 3', 
                            'reserve_pool_timeout = 2', 
                            'log_connections = 1', 
                            'log_disconnections = 1', 
                            'log_pooler_errors = 1', 
                            'server_lifetime = 10800', 
                            'server_idle_timeout = 300', 
                            'server_connect_timeout = 15', 
                            'server_login_retry = 7', 
                            'query_wait_timeout = 3600', 
                            'client_login_timeout = 0', 
                            'autodb_idle_timeout = 3600',
                            'logfile = /u00/app/postgres/admin/logs/pgbouncer/stb_' + self.stbname,
                            'pidfile = ' + self.sshclient.execute('echo $STBVARDIR/stb_$STBNAME.pid')]),
                            ('pgbStatUsers', 'monitoring'),
                            ('pgHome', self.sshclient.execute('echo $HOME')),
                            ('pgVersCompat', self.getStbVersion())]
            self.ldif2LDAP['cn=dblinks,' + dn] = [('cn', 'dblinks'),
                                                  ('objectClass', ['rbcContainer', 'top'])]
            self.ldif2LDAP['cn=users,' + dn] = [('cn', 'users'),
                                                  ('objectClass', ['rbcContainer', 'top'])]

        elif action == 'MODIFY':
            self.ldif2LDAP[dn] = [(self.ldapModeModify(dn, 'dbaServiceType'), 'dbaServiceType', 'PgBouncer'),
                                        (self.ldapModeModify(dn, 'dbaHostName'), 'dbaHostName', self.dbaHostName),
                                        (self.ldapModeModify(dn, 'stdMode'), 'stdMode', self.stbmode),
                                        (self.ldapModeModify(dn, 'dbaPort'), 'dbaPort', str(self.dbaport)),
                                        (self.ldapModeModify(dn, 'pgUser'), 'pgUser', 'postgres'),
                                        (self.ldapModeModify(dn, 'dbaConfig'), 'dbaConfig', self.sshclient.execute('echo ${STBCONFDIR}/${STBNAME}/config_ldap.ini')),
                                        (self.ldapModeModify(dn, 'pgbAdminUsers'), 'pgbAdminUsers', 'ss'),
                                        (self.ldapModeModify(dn, 'pgbConfigSettings'), 'pgbConfigSettings', ['listen_addr =  *',
                                        'listen_port = ' + str(self.dbaport), 
                                        'unix_socket_dir = /tmp',
                                        'server_reset_query = RESET ALL; SET SESSION AUTHORIZATION DEFAULT; SET SESSION ROLE TO DEFAULT;',
                                        'ignore_startup_parameters = extra_float_digits, application_name',
                                        'server_check_query = SELECT 1',
                                        'server_check_delay = 10',
                                        'max_client_conn = 500',
                                        'default_pool_size = 50',
                                        'reserve_pool_size = 3',
                                        'reserve_pool_timeout = 2',
                                        'log_connections = 1',
                                        'log_disconnections = 1',
                                        'log_pooler_errors = 1',
                                        'server_lifetime = 10800',
                                        'server_idle_timeout = 300',
                                        'server_connect_timeout = 15',
                                        'server_login_retry = 7',
                                        'query_wait_timeout = 3600',
                                        'client_login_timeout = 0',
                                        'autodb_idle_timeout = 3600',
                                        'logfile = /u00/app/postgres/admin/logs/pgbouncer/stb_' + self.stbname,
                                        'pidfile = ' + self.sshclient.execute('echo $STBVARDIR/stb_$STBNAME.pid')]),
                                        (self.ldapModeModify(dn, 'pgbStatUsers'), 'pgbStatUsers', 'monitoring'),
                                        (self.ldapModeModify(dn, 'pgHome'), 'pgHome', self.sshclient.execute('echo $HOME')),
                                        (self.ldapModeModify(dn, 'pgVersCompat'), 'pgVersCompat', self.getStbVersion())]


    def prepareAliasAdd2LDAP(self, dn, aliasname, aliasdn):
        self.ldif2LDAP[dn] = [('cn' , aliasname),
                            ('objectClass', ['top', 'alias', 'extensibleObject']),
                            ('aliasedObjectName', aliasdn)]

            
    def update2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgbounceradmin', 'uid=pgbounceradmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in self.ldif2LDAP:
                    self.ldap.modify_s(rldif, self.ldif2LDAP[rldif]) 
            except Exception, e:
                stdOut.write(str(e) + '\n')
            finally:
                self.ldap.bind_s('','')


    def add2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgbounceradmin', 'uid=pgbounceradmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rldif in sorted(self.ldif2LDAP, key=lambda key: len(key.split('cn='))):
                    try: 
                        self.ldap.add_s(rldif, self.ldif2LDAP[rldif]) 
                    except Exception, e:
                        stdOut.write('ERROR: ' + str(e) + '\nAdd to LDAP dn: ' + str(rldif) + '\nLDIF: ' + str(self.ldif2LDAP[rldif]) + '\nlogin: ' + str(login) + ' passw: ' + str(passw[:1]) + '****' + str(passw[-1:]) + '\n')
            finally:
                self.ldap.bind_s('','')


    def changeConfigTemplate(self, confile):
        stdOut.write("\nПытаемся получить шаблоны обновления файла конфигурации для PgBouncer...\n")
        b_frm_ldap = self.getTemplateBodyFromLDAP(confile)
        if not b_frm_ldap is None: 
            for dn, rattr in b_frm_ldap:
                for attr in rattr['pgbConfigSettings']:
                    self.sshclient.execute('if grep -Fq "'+ attr +'" ${STBCONFDIR}/${STBNAME}/config_ldap.ini; then sed -i "s,^' + attr + ' =.*$,' + attr +'," ${STBCONFDIR}/${STBNAME}/config_ldap.ini; else echo "' + attr + '" >> ${STBCONFDIR}/${STBNAME}/config_ldap.ini; fi')
                stdOut.write("Применен шаблон обновления для PostgreSQL\nфайла конфигурации в LDAP\n\n")
        else:
            stdOut.write("\nшаблонов обновления для файла конфигурации не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")
        
        
    def registerPgBouncerLDAP(self):
        self.stbConfigTemplateSet('stb_config_ldap', '${STBCONFDIR}/${STBNAME}/config_ldap.ini')
        try:
            self.ldif2LDAP = {}
            if self.check2LDAP() == None:
                self.prepare2LDAP('cn=' + self.stbname + ',cn=PgBouncers,cn=PgContext,dc=rbc,dc=ru', 'ADD')
                self.add2LDAP()
            else:
                self.prepare2LDAP('cn=' + self.stbname + ',cn=PgBouncers,cn=PgContext,dc=rbc,dc=ru', 'MODIFY')
                self.update2LDAP()
        except Exception, e:
            stdOut.write('Ошбка внесения изменений в LDAP\n' + str(e) + '\n')
            return
        self.changeConfigTemplate('stb_conf')
        self.registerPgAdminStatUsers(self.stbname)


    def registerPgAdminStatUsers(self, stbname):
        self.ldif2LDAP = {}
        b_frm_ldap = self.getPgAdminStatUsersFromLDAP(stbname)
        if not b_frm_ldap is None: 
            for dn, rattr in b_frm_ldap:
                for attr in rattr:
                    for ruser in ''.join(rattr[attr]).split(','):
                        self.prepareAliasAdd2LDAP('cn=' + ruser + ',cn=users,cn=' + stbname + ',cn=PgBouncers,cn=PgContext,dc=rbc,dc=ru', ruser, 'uid=' + ruser + ',ou=Users,dc=rbc,dc=ru')
            self.add2LDAP()
            stdOut.write("Установлены пользователи администрирования и статистики для PgBouncer...\n")
        else:
            stdOut.write("\nПользователей для администрирования и статистики не найдено.\nПри необходимости добавьте их вручную...\n")
        

    def getTemplateBodyFromLDAP(self, templtype):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + templtype + ',cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['pgbConfigSettings', 'pgContribName'])
            
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def getPgAdminStatUsersFromLDAP(self, stbname):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + stbname + ',cn=PgBouncers,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_BASE,'(cn=*)', ['pgbAdminUsers','pgbStatUsers'])
            
        except Exception, e:
            stdOut.write(str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr

        
    def stbConfigTemplateSet(self, confile, confdest):
        stdOut.write("\nПытаемся получить шаблоны стандарного файла конфигурации для БД PostgreSQL...\n")
        b_frm_ldap = self.getTemplateBodyFromLDAP(confile)
        if not b_frm_ldap is None: 
            for dn, rattr in b_frm_ldap:
                self.sshclient.execute('echo "' + base64.b64encode(''.join(rattr['pgbConfigSettings'])) + '" | base64 -d > ' + confdest)
                self.sshclient.execute('chmod 640 ' + confdest)
                stdOut.write("Применен стандартный шаблон для PostgreSQL\nфайла конфигурации " + confile + " на " + confdest + "\n\n")
        else:
            stdOut.write("\nСтандартных шаблонов для файла конфигурации не найдено.\nПри необходимости исправьте конфигурацию вручную...\n")


class pgDatabaseAdm():        
    TEMPL_CMD_STRING_CREA = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/psql -p %s -c "CREATE DATABASE %s WITH OWNER=postgres ENCODING='+"'%s'" + ' TABLESPACE=%s LC_COLLATE=' + "'ru_RU.UTF8' LC_CTYPE='ru_RU.UTF8'" + ' CONNECTION LIMIT=-1 TEMPLATE=%s"'
    TEMPL_CMD_STRING_TBLSPC_TODB = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/psql -p %s -c "ALTER DATABASE %s SET TABLESPACE %s"'
    TEMPL_CMD_STRING_TBLSPC_CREA = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;PGPORT=%s;TBSPC=%s;mkdir -p $PGDATA/tablespaces/$TBSPC && chmod 700 $PGDATA/tablespaces/$TBSPC && $PGHOME/bin/psql -p $PGPORT -c "CREATE TABLESPACE $TBSPC LOCATION ' + "'$PGDATA/tablespaces/$TBSPC'" + '"'
    TEMPL_CMD_STRING_TBLSPC_DROP = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;PGPORT=%s;TBSPC=%s;$PGHOME/bin/psql -p $PGPORT -c "DROP TABLESPACE $TBSPC"'
    TEMPL_CMD_STRING_TBLSPC_RENAME = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;PGPORT=%s;TBSPCFROM=%s;TBSPCTO=%s;$PGHOME/bin/psql -p $PGPORT -c "ALTER TABLESPACE $TBSPCFROM RENAME TO $TBSPCTO"'
    TEMPL_CMD_STRING_TBLSPC_COMMENT = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;PGPORT=%s;TBSPC=%s;$PGHOME/bin/psql -p $PGPORT -c "COMMENT ON TABLESPACE $TBSPC IS ' + "'%s'" + '"'
    TEMPL_CMD_STRING_TBLSPC_OBJECT_SET = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/psql -p %s %s -c "ALTER %s %s.%s SET TABLESPACE %s"'
    TEMPL_CMD_STRING_RUN_COMMAND = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/psql -p %s %s -f %s'
    TEMPL_CMD_STRING_ROLE_CREA = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;PGPORT=%s;PGROLE=%s;PGROLENC=%s;PGROLETS=%s;PGROLESP=%s;$PGHOME/bin/psql -p $PGPORT -c "CREATE ROLE $PGROLE LOGIN NOSUPERUSER INHERIT NOCREATEDB NOCREATEROLE NOREPLICATION;"; if [ ! -z $PGROLENC ]; then $PGHOME/bin/psql -p $PGPORT -c "ALTER ROLE $PGROLE SET client_encoding = ' + "'$PGROLENC';" + '"; fi; if [ ! -z $PGROLETS ]; then $PGHOME/bin/psql -p $PGPORT -c "ALTER ROLE $PGROLE SET default_tablespace = ' + "'$PGROLETS';" + '"; fi; if [ ! -z $PGROLESP ]; then $PGHOME/bin/psql -p $PGPORT -c "ALTER ROLE $PGROLE SET search_path = $PGROLESP;"; fi'
    TEMPL_CMD_STRING_SCHEMA_CREA = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/psql -p %s %s -c "CREATE SCHEMA %s AUTHORIZATION %s;"'
    TEMPL_CMD_STRING_UPLOAD_CONF = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;PGPORT=%s;echo "%s" | base64 -d > $PGDATA/%s && $PGHOME/bin/pg_ctl -p $PGPORT -D $PGDATA reload'
    TEMPL_CMD_STRING_ROLE_CONFIG = 'ENVFILE=`echo %s | sed "s/\(stdb_\)*/\\1env_pg_/"`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/psql -tq -p %s -c "SELECT useconfig FROM pg_user WHERE usename = ' + "'%s'" + ';"'
    
    exit_status = 1001
    dbaPort = 0
    pgClusterName = ''
    dbaHostName = ''
    sqlCommand = ''
    pgTablespace = 'pg_default'
    pgTablespaceFrom = ''
    pgTablespaceTo = ''
    pgTablespaceComment = ''
    pgObjectType = ''
    pgSchemaName = ''
    pgObjectName = ''
    dbName = ''
    sqlCommandFile = ''
    dbEncoding = 'UTF8'
    dbTemplate = 'template1'
    schemaName = ''
    schemaOwner = ''
    roleSearchPath = ''
    ConfFileName = ''
    ConfFileText = ''
    command_result = ''
        
    def __init__(self):
        self.classCommands()
        
        
    def classCommands(self):
        self.command_attrs={"create_database":        self.TEMPL_CMD_STRING_CREA%(self.pgClusterName, self.dbaPort, self.dbName, self.dbEncoding, self.pgTablespace, self.dbTemplate),
                            "settbl_database":        self.TEMPL_CMD_STRING_TBLSPC_TODB%(self.pgClusterName, self.dbaPort, self.dbName, self.pgTablespace),
                            "create_tablespace":      self.TEMPL_CMD_STRING_TBLSPC_CREA%(self.pgClusterName, self.dbaPort, self.pgTablespace),
                            "rename_tablespace":      self.TEMPL_CMD_STRING_TBLSPC_RENAME%(self.pgClusterName, self.dbaPort, self.pgTablespaceFrom, self.pgTablespaceTo),
                            "drop_tablespace":        self.TEMPL_CMD_STRING_TBLSPC_DROP%(self.pgClusterName, self.dbaPort, self.pgTablespace),
                            "comment_tablespace":     self.TEMPL_CMD_STRING_TBLSPC_COMMENT%(self.pgClusterName, self.dbaPort, self.pgTablespace, self.pgTablespaceComment),
                            "set_object_tablespace":  self.TEMPL_CMD_STRING_TBLSPC_OBJECT_SET%(self.pgClusterName, self.dbaPort, self.dbName, self.pgObjectType, self.pgSchemaName, self.pgObjectName, self.pgTablespace),
                            "run_command":            self.TEMPL_CMD_STRING_RUN_COMMAND%(self.pgClusterName, self.dbaPort, self.dbName, self.sqlCommandFile),
                            "create_user":            self.TEMPL_CMD_STRING_ROLE_CREA%(self.pgClusterName, self.dbaPort, self.schemaOwner, self.dbEncoding, self.pgTablespace, self.roleSearchPath),
                            "create_schema":          self.TEMPL_CMD_STRING_SCHEMA_CREA%(self.pgClusterName, self.dbaPort, self.dbName, self.schemaName, self.schemaOwner),
                            "upload_conf_file":       self.TEMPL_CMD_STRING_UPLOAD_CONF%(self.pgClusterName, self.dbaPort, self.ConfFileText, self.ConfFileName),
                            "get_user_config":        self.TEMPL_CMD_STRING_ROLE_CONFIG%(self.pgClusterName, self.dbaPort, self.schemaOwner)
                            }
    
    def pgGetUserConfig(self, username):
        rtr = {}
        self.schemaOwner = username
        self.classCommands()
        self.pgActionWithSUDO(self.command_attrs["get_user_config"])
        if self.command_result != '':
            self.command_result = self.command_result.replace('{', '').replace('}', '')
            try:
                rtr['client_encoding'] = self.command_result.split('client_encoding=')[1].split(',')[0].replace('\n','')
            except:
                pass
            try:
                rtr['default_tablespace'] = self.command_result.split('default_tablespace=')[1].split(',')[0].replace('\n','')
            except:
                pass
            try:            
                rtr['search_path'] = self.command_result.split('search_path=')[1].split('"')[0].replace('\n','')
            except:
                pass
        return rtr
        
    def pgRelatedCommand(self, action):
        self.classCommands()
        self.pgActionWithSUDO(self.command_attrs[action])

        
    def pgActionWithSUDO(self, command):
        self.command_result = ''
        sshclient = SSHConnector(self.dbaHostName)
        if sshclient.sshchannel != None:
            try:
                stdOut.write('\nПытаемся выполнить команду psql ' + command + '\n')
                self.command_result = sshclient.execute(command)
                if sshclient.exit_status == 0:
                    stdOut.write('\nВыполнение команды успешно завершено...\n')
                else:
                    stdOut.write(self.command_result + '\n')
                    stdOut.write('\nВыполнение команды завешилось неудачно...\n')
            except Exception, e:
                stdOut.write('Ошибка получения SUDO\n' + str(e) + '\n')
                self.exit_status = 1001
            finally:
                self.exit_status = sshclient.exit_status


class pgBouncerAdm():        
    TEMPL_CMD_STRING_START = 'cd %s;export LD_LIBRARY_PATH=%s/lib:$LD_LIBRARY_PATH;export COLUMNS=512; %s/bin/pgbouncer -d %s'
    TEMPL_CMD_STRING_STOP = 'cd %s;export LD_LIBRARY_PATH=%s/lib:$LD_LIBRARY_PATH;export COLUMNS=512; ps axf | grep pgbouncer | grep \"%s\" | grep -v grep | awk '+ "'" + '{print $1}' + "'" + '| xargs --no-run-if-empty kill -9'
    TEMPL_CMD_STRING_RELOAD = 'cd %s;export LD_LIBRARY_PATH=%s/lib:$LD_LIBRARY_PATH;export COLUMNS=512; psql -c "RELOAD" "host=/tmp port=%s user=%s password=%s dbname=pgbouncer"'
    TEMPL_CMD_STRING_KILLDB = 'cd %s;export LD_LIBRARY_PATH=%s/lib:$LD_LIBRARY_PATH;export COLUMNS=512; psql -c "KILL %s" "host=/tmp port=%s user=%s password=%s dbname=pgbouncer"'

    exit_status = 1001
    dbaPort = 0
    pgHome = ''
    dbaHostName = ''
    loginpassw = ('','')
    dbaConfig = ''
    dbname = ''
    

    def __init__(self):
        self.classCommands()
        
        
    def classCommands(self):
        self.command_attrs={"start":          self.TEMPL_CMD_STRING_START%(self.pgHome,self.pgHome,self.pgHome,self.dbaConfig),
                            "stop":           self.TEMPL_CMD_STRING_STOP%(self.pgHome,self.pgHome,self.dbaConfig),
                            "reload":         self.TEMPL_CMD_STRING_RELOAD%(self.pgHome,self.pgHome,self.dbaPort,self.loginpassw[0],self.loginpassw[1]),
                            "killdb":         self.TEMPL_CMD_STRING_KILLDB%(self.pgHome,self.pgHome,self.dbname,self.dbaPort,self.loginpassw[0],self.loginpassw[1])
                            }
    
    
    def pgRelatedCommand(self, action):
        if (action == 'stop') or (action == 'reload') or (action == 'killdb'):
            self.loginpassw = dlgLoginPasswInput.AuthFromKeyring('LDAP')
        self.classCommands()
        self.pgActionWithSUDO(self.command_attrs[action])

        
    def pgActionWithSUDO(self, command):
        self.command_result = ''
        sshclient = SSHConnector(self.dbaHostName)
        if sshclient.sshchannel != None:
            try:
                stdOut.write('\nПытаемся выполнить команду psql ' + command + '\n')
                self.command_result = sshclient.execute(command)
                if sshclient.exit_status == 0:
                    stdOut.write('\nВыполнение команды успешно завершено...\n')
                else:
                    stdOut.write(self.command_result + '\n')
                    stdOut.write('\nВыполнение команды завешилось неудачно...\n')
            except Exception, e:
                stdOut.write('Ошибка получения SUDO\n' + str(e) + '\n')
                self.exit_status = 1001
            finally:
                self.exit_status = sshclient.exit_status
        return

    
class pgClusterAdm():        
    TEMPL_CMD_STRING_START = "ENVFILE=`echo %s | sed 's/\(stdb_\)*/\\1env_pg_/'`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/pg_ctl start -w -t 60 -D $PGDATA"
    TEMPL_CMD_STRING_STOP = "ENVFILE=`echo %s | sed 's/\(stdb_\)*/\\1env_pg_/'`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/pg_ctl stop -D $PGDATA -m fast -w -t 30"
    TEMPL_CMD_STRING_RELOAD = "ENVFILE=`echo %s | sed 's/\(stdb_\)*/\\1env_pg_/'`.sh;cd;source ~/env/$ENVFILE;$PGHOME/bin/pg_ctl reload -D $PGDATA"

    exit_status = 1001
    dbaHostName = ''
    pgClusterName = ''
    

    def __init__(self):
        self.classCommands()
               
               
    def classCommands(self):
        self.command_attrs={"start":          self.TEMPL_CMD_STRING_START%(self.pgClusterName),
                            "stop":           self.TEMPL_CMD_STRING_STOP%(self.pgClusterName),
                            "reload":         self.TEMPL_CMD_STRING_RELOAD%(self.pgClusterName)
                            }
    
    
    def pgRelatedCommand(self, action):
        self.classCommands()
        self.pgActionWithSUDO(self.command_attrs[action])

        
    def pgActionWithSUDO(self, command):
        self.command_result = ''
        sshclient = SSHConnector(self.dbaHostName)
        if sshclient.sshchannel != None:
            try:
                stdOut.write('\nПытаемся выполнить команду pg_ctl ' + command + '\n')
                self.command_result = sshclient.execute(command)
                if sshclient.exit_status == 0:
                    stdOut.write('\nВыполнение команды успешно завершено...\n')
                else:
                    stdOut.write(self.command_result + '\n')
                    stdOut.write('\nВыполнение команды завешилось неудачно...\n')
            except Exception, e:
                stdOut.write('Ошибка получения SUDO\n' + str(e) + '\n')
                self.exit_status = 1001
            finally:
                self.exit_status = sshclient.exit_status
        return

    
class SSHConnector(paramiko.Channel):
    sshchannel = None
    sshsession = None
    timeout = 600
    exit_status = 1001
    def __init__(self, dbaHostName):
        self.dbaHostName = dbaHostName
#        paramiko.Channel.__init__(self, self.sshchannel)
        self.initSSH()
        
    def __del__(self):
        self.close()

    def initSSH(self):
        self.sshsession = paramiko.SSHClient()
        self.sshsession.load_system_host_keys()
        self.sshsession.set_missing_host_key_policy(paramiko.AutoAddPolicy())
        (login,passw) = dlgLoginPasswInput.AuthFromKeyring(self.dbaHostName) 
         
        try:
            self.sshsession.connect(hostname=self.dbaHostName,username=login,password=passw)
        except paramiko.AuthenticationException, e:
            stdOut.write('Ошибка авторизации '+ login +'\n' + str(e) + '\n')
            return 1100
        try:
            self.sshchannel = self.sshsession.invoke_shell()
#            self.sshchannel.get_pty()
            self.sshchannel.settimeout(300)
            self.sshchannel.setblocking(True)
            while not self.sshchannel.recv_ready():            
                time.sleep(1)
            while self.sshchannel.recv_ready():
                stdout = self.sshchannel.recv(1024)
            while not ((stdout.split('\r\n')[-1].strip() != '') and (stdout.split('\r\n')[-1].strip()[-1] == '$')):
                stdout = self.getResult()
            stdout = ''
            self.sshchannel.send('whoami\n')
            while not self.sshchannel.recv_ready():
                time.sleep(0.5)
            while self.sshchannel.recv_ready():
                stdout = self.sshchannel.recv(1024)
            if stdout.split('\r\n')[0] == 'whoami' and stdout.split('\r\n')[1] != 'postgres':
                self.sshchannel.send('sudo -s -H -u postgres\n')
                while not self.sshchannel.recv_ready():
                    time.sleep(0.5)
                while self.sshchannel.recv_ready():
                    stdout = self.sshchannel.recv(1024)
            if not "$" in stdout:
                self.sshchannel.send(passw+'\n')
                time.sleep(0.5)
            while self.sshchannel.recv_ready():
                self.sshchannel.recv(1024)
            
        except paramiko.ChannelException, e:
            stdOut.write('Ошибка инициализации сесии в главном модуле\n' + str(e) + '\n')
        return 0
        
    def execute(self, command, wResult = False, wOut = stdOut):
        rtr = ''
        rtr_sub = ''
#         statrtime = datetime.datetime.now()
        self.sshchannel.send(command + '; echo $?' +'\n')
        rtr = self.getResult()
        try:
            while not ((rtr.split('\r\n')[-1].strip() != '') and (rtr.split('\r\n')[-1].strip()[-1] == '$')):
#                 if datetime.datetime.now() - statrtime < datetime.timedelta(seconds=self.timeout):
                if wResult:
                    if rtr_sub == '':
                        wOut.write(rtr)
                    else:
                        wOut.write(rtr_sub)
                rtr_sub = self.getResult()
                rtr += rtr_sub
#                 else:
#                     self.exit_status = 1003
#                     return rtr
            self.exit_status = int(rtr.split('\r\n')[-2])
        except Exception, e:
            wOut.write('Ошибка в выполнении команды ssh: ' + str(e) + '\nкоманды: ' + command + '\nрезультат: ' + rtr + '\n')
            self.exit_status = 1001
        rtr = '\n'.join(rtr.split('\r\n')[1:-2])
        if wResult:
            if rtr_sub == '':
                wOut.write(rtr + '\n')
            else:
                wOut.write('\n'.join(rtr_sub.split('\r\n')[1:-2]) + '\n')
        return rtr
        
    def getResult(self):
        rtr = ''
        while not self.sshchannel.recv_ready():
            time.sleep(0.5)
        while self.sshchannel.recv_ready():
            rtr += self.sshchannel.recv(1024)
        return rtr
        
    def putfile(self, filesource, filedest, wOut = stdOut):
        rtr = ''
        try:
            with SCPClient(self.sshchannel.get_transport()) as scp:
                scp.put(filesource, filedest)
                self.exit_status = 0
        except Exception, e:
            wOut.write('Ошибка в выгрузке файла ' + filesource + ' на локальный файл ' + filedest + '\n' + str(e) + '\n')
        finally:
            return rtr
        
    def close(self):
        self.sshchannel.close()
        self.sshsession.close()
        
        
class dlgUpdate2LDAP(gtk.Dialog):
    def __init__(self, parent):
        gtk.Dialog.__init__(self, "Сохранить изменения в LDAP", parent, 0, (gtk.STOCK_OK, gtk.RESPONSE_ACCEPT, gtk.STOCK_CANCEL, gtk.RESPONSE_CANCEL))
        self.set_default_size(250, 100)
        box = self.get_content_area()
        box.add(gtk.Label("Сохранить изменения в LDAP?"))
        self.show_all()


class dlgAuthUsersAdm(gtk.Dialog):
    curlogin = ""
    
    def __init__(self):
        gtk.Dialog.__init__(self, "Редактирование пользователей в keyring", None, 0)
        self.set_default_size(650, 500)
        box = self.get_content_area()
        self.lslogins = gtk.ListStore('gchararray')
        self.tvlogins = gtk.TreeView(self.lslogins)
        cell = gtk.CellRendererText()
        col = gtk.TreeViewColumn(None, cell, text=0)
        self.tvlogins.append_column(col)
        self.tvlogins.connect('cursor-changed', self.tvloginsChanged)
        self.scrolledwindow = gtk.ScrolledWindow()
        self.scrolledwindow.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_ALWAYS)
        self.scrolledwindow.add_with_viewport(self.tvlogins)
        self.lbpassword = gtk.Label('')
        self.btClearPassword = gtk.Button("Сбросить пароль")
        self.btClearPassword.set_size_request(80,25)
        self.btClearPassword.connect("clicked", self.btClearPasswordClicked)
        
        vbox = gtk.VBox(False, 3)
        vbox.pack_start(self.scrolledwindow)
        vbox.pack_end(self.btClearPassword, False, False)
        vbox.pack_end(self.lbpassword, False, False)
        box.add(vbox)
        self.show_all()
        
        self.drawTvlogins()

    def drawTvlogins(self):
        for r in gk.list_item_ids_sync('clientad'):
            item = gk.item_get_info_sync('clientad', r)
            self.lslogins.append([item.get_display_name()])

    def tvloginsChanged(self, subject):
        path = subject.get_cursor()[0]
        m = subject.get_model()
        for r in gk.list_item_ids_sync('clientad'):
            item = gk.item_get_info_sync('clientad', r)
            if item.get_display_name() ==  m.get_value(m.get_iter(path), 0):
                self.curlogin = r
                self.lbpassword.set_text(item.get_secret())
         
        
    def btClearPasswordClicked(self, subject):
        gk.item_delete_sync('clientad', self.curlogin)
        self.lslogins.clear()
        self.drawTvlogins()
    
class dlgDrawDatabasesFromClusters(gtk.Dialog):
    def __init__(self, app_main):
        gtk.Dialog.__init__(self, "Получение списка баз данных по кластерам", None, 0)
        self.set_default_size(650, 500)
        box = self.get_content_area()
        self.lstree = gtk.TextBuffer()
        self.tvtree = gtk.TextView(self.lstree)
        self.scrolledwindow = gtk.ScrolledWindow()
        self.scrolledwindow.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_ALWAYS)
        self.scrolledwindow.add_with_viewport(self.tvtree)
        
        vbox = gtk.VBox(False, 3)
        vbox.pack_start(self.scrolledwindow)
        box.add(vbox)
        self.show_all()
        
        self.lstree.set_text('\n'.join(app_main.drawClustersAndDatabases()))


class dlgSearch(gtk.MessageDialog):
    def __init__(self):        
        gtk.MessageDialog.__init__(self,None,
           gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT,
           gtk.MESSAGE_QUESTION,
           gtk.BUTTONS_OK, None)
        self.search_text = gtk.Entry()
        self.set_markup('Ключевое слово для поиска')
        self.vbox.pack_end(self.search_text)
        self.search_text.connect("activate", self.responseToDialog, self, gtk.RESPONSE_ACCEPT)
        self.show_all()

    @staticmethod
    def responseToDialog(entry, dialog, response):
        dialog.response(response)
        
    @staticmethod
    def getSearch(dialog):
        res = {'result': False, 'dialog': dialog, 'text_search': ""}
        if dialog == None:
            dialog = dlgSearch()
            res['dialog'] = dialog
        res['result'] = dialog.run() == gtk.RESPONSE_ACCEPT
        res['text_search'] = dialog.search_text.get_text()
        if not res['result']:
            dialog.destroy()
        return res


class dlgLoginPasswInput(gtk.Dialog):
    edpassw = gtk.Entry()
    edlogin = gtk.Entry()
    checksave = gtk.CheckButton("Сохранить пароль в keyring?")
    
    def __init__(self, parent, caption = 'Авторизация', defaultlogin = ''):
        gtk.Dialog.__init__(self, caption, parent, 0, (gtk.STOCK_OK, gtk.RESPONSE_ACCEPT, gtk.STOCK_CANCEL, gtk.RESPONSE_CANCEL))
        self.set_default_response(gtk.RESPONSE_ACCEPT)
        self.set_default_size(250, 100)
        box = self.get_content_area()
        box.add(gtk.Label("Логин"))
        self.edlogin.set_text(defaultlogin)
        box.add(self.edlogin)
        box.add(gtk.Label("Пароль"))
        self.edpassw.set_visibility(False)
        box.add(self.edpassw)
        box.add(self.checksave)
        self.show_all()

    @staticmethod
    def getLoginPasswFromInput(msg, defaultlogin = ''):
        rtr = ('', '', False)
        gtk.threads_init()
        gtk.threads_enter()
        try:
            dialog = dlgLoginPasswInput(None, msg, defaultlogin)
            response = dialog.run()
            if response == gtk.RESPONSE_ACCEPT:
                rtr = (dialog.edlogin.get_text(), dialog.edpassw.get_text(), dialog.checksave)
            dialog.hide_all()
            dialog.destroy()
        finally:
            gtk.threads_leave()            
        return rtr

    @staticmethod
    def AuthFromKeyring(objname, defaultlogin = ''):
        keyring = 'clientad' 
        rtr = ()
        if keyring in gk.list_keyring_names_sync():
            try:
                item = gk.find_items_sync(gk.ITEM_NO_TYPE,{'objectype': objname})[0]
                rtr = (item.attributes['username'], item.secret)
            except gk.NoMatchError:
                rtr = dlgLoginPasswInput.getLoginPasswFromInput('Авторизация ' + objname, defaultlogin)
                if rtr[2].get_active():
                    gk.item_create_sync(keyring, gk.ITEM_NO_TYPE, rtr[0] + '_' + objname,{'username': rtr[0], 'objectype': objname}, rtr[1], True)
        else:
            gk.create_sync(keyring, None)
            rtr = dlgLoginPasswInput.getLoginPasswFromInput('Авторизация ' + objname, defaultlogin)
            if rtr[2].get_active():
                gk.item_create_sync(keyring, gk.ITEM_NO_TYPE, rtr[0] + '_' + objname,{'username': rtr[0], 'objectype': objname}, rtr[1], True)
        return (rtr[0], rtr[1])


class dlgMultiLineText(gtk.Dialog):
    
    def __init__(self, parent, caption='Редактор строки'):
        gtk.Dialog.__init__(self, caption, parent, 0, (gtk.STOCK_OK, gtk.RESPONSE_ACCEPT, gtk.STOCK_CANCEL, gtk.RESPONSE_CANCEL))
        self.set_default_response(gtk.RESPONSE_ACCEPT)
        self.set_default_size(480, 360)
        box = self.get_content_area()
        self.edText = gtk.TextView()
        self.edText.connect("key-press-event", self.edTextKeyPress)
                # Syntax definition
        ips=Pattern(r"\b(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)|\/([0-3]|[0-2][0-9]|[3][0-2])\b", style="number")
        coment  = Pattern(r"#.*$", style="comment")
        eq = Pattern(r"\b(md5|trust)\b", style="datatype")
        num = Pattern(r"\b(\d+|\d+(MB)|\d+(KB)|\d+(GB))\b", style="number")

        lang = LanguageDefinition([num, eq, ips, coment])

        buff = CodeBuffer(lang=lang)
        self.edText.set_buffer(buff)

        self.edText.set_wrap_mode(gtk.WRAP_WORD)
        self.textbuff = self.edText.get_buffer()
        
        scrolled_window = gtk.ScrolledWindow()
        scrolled_window.add(self.edText)
        box.add(scrolled_window)
        self.show_all()

    @staticmethod        
    def doEdit(self, msg):
        rtr = msg
#        gtk.threads_init()
#        gtk.threads_enter()

        try:
            dialog = dlgMultiLineText(None)
            dialog.textbuff.set_text(msg)
            response = dialog.run()
            if response == gtk.RESPONSE_ACCEPT:
                rtr = dialog.textbuff.get_text(dialog.textbuff.get_start_iter(), dialog.textbuff.get_end_iter())
            dialog.hide_all()
            dialog.destroy()
        finally:
            pass
#            gtk.threads_leave()            
        return rtr


    def findText(self, text_search, iter):
        res = {'result': False, 'iter': iter}
        match_start = None
        match_end = None
        buf = self.edText.get_buffer()
        if iter == None:
            start_iter = buf.get_start_iter()
        else:
            start_iter = iter
        found = start_iter.forward_search(text_search,0, None) 
        if found:
            match_start, match_end = found #add this line to get match_start and match_end
            buf.select_range(match_start,match_end)
            self.edText.scroll_to_iter(match_start, 0)
        res['result'] = found != None
        res['iter'] = match_end
        return res


    def edTextKeyPress(self, subject, event):
        self.filebodychanged = [True, True]
        if event.state & gtk.gdk.CONTROL_MASK:
            if gtk.gdk.keyval_name(event.keyval).upper() == "F":
                f = dlgSearch.getSearch(None)
                fnd = {'result': False, 'iter': None}
                while f['result']:  
                    fnd = self.findText(f['text_search'], fnd['iter'])
                    if not fnd['result']:
                        sys.stdout.write("Искомый текст не найден\n")
                        f['dialog'].destroy()
                        break
                    f = dlgSearch.getSearch(f['dialog'])           


class cVTerminal(vte.Terminal):
    vpid = 0 
    
    def __init__(self, pghostname, login):
        super(cVTerminal, self).__init__()
        self.configure_terminal()
        params = ["ssh",
                              login+ "@" +
                              pghostname]
        self.vpid = self.fork_command('ssh', params)
        self.show()
       
    def configure_terminal(self):
        palette = [gtk.gdk.color_parse('#2E2E34343636'),gtk.gdk.color_parse('#CCCC00000000'),gtk.gdk.color_parse('#4E4E9A9A0606'),gtk.gdk.color_parse('#C4C4A0A00000'),gtk.gdk.color_parse('#34346565A4A4'),gtk.gdk.color_parse('#757550507B7B'),gtk.gdk.color_parse('#060698209A9A'),gtk.gdk.color_parse('#D3D3D7D7CFCF'),gtk.gdk.color_parse('#555557575353'),gtk.gdk.color_parse('#EFEF29292929'),gtk.gdk.color_parse('#8A8AE2E23434'),gtk.gdk.color_parse('#FCFCE9E94F4F'),gtk.gdk.color_parse('#72729F9FCFCF'),gtk.gdk.color_parse('#ADAD7F7FA8A8'),gtk.gdk.color_parse('#3434E2E2E2E2'),gtk.gdk.color_parse('#EEEEEEEEECEC')]
        self.set_colors(gtk.gdk.color_parse('black'), gtk.gdk.color_parse('white'), palette)
        self.set_scrollback_lines(500)
        self.set_encoding("UTF-8")
        self.set_word_chars("-A-Za-z0-9,./?%&#:_")
        font = pango.FontDescription()
        font.set_family("Monospace")
        font.set_size(9 * pango.SCALE)
        font.set_weight(pango.WEIGHT_NORMAL)
        font.set_stretch(pango.STRETCH_NORMAL)
        self.set_font_full(font, True)



#=====================================================================



class App_main(gtk.Builder):
    list_excluded_users = ['pgadmin','pgbounceradmin','pgnetadmin','pgnetuser','pgregcontrib','pgregdbs','pgskadmin','pguser','pgusersearch', 'replicator','context','monitoring']
    list_excluded_netservices = []
        
    def __init__(self):
        super(App_main, self).__init__()
        self.add_from_file(dirpath+'/fclient2.ui')
        self.ldap = ldap.initialize('ldap://' + ldap_host + ':' + ldap_port)
        self.pgBouncerDetailType = {'Базы данных': 'dblinks', 'Пользователи': 'users', 'Общие настройки': ''}
        self.pgClusterDetailType = {'Базы данных': 'dbs', 'Пользователи': 'users', 'Библиотеки': 'contribs', 'Skytools': 'skytools', 'Общие настройки': '', 'Файлы настроек БД': 'confiles', 'wal': 'WRITE AHEAD LOG', 'auth': 'CONNECTIONS AND AUTHENTICATION', 'resource': 'RESOURCE USAGE (except WAL)', 'log': 'ERROR REPORTING AND LOGGING'}
        self.ldif2LDAP = {}
        self.SysLogSession = None
        self.currentToolButtonPosition=""
        
        
#---------------Get Objects ++++++++++++++++++++++++

        
        self.fmain = self.get_object("fmain")
        self.tbmain = self.get_object("tbmain")
        self.tbclust = self.get_object("tbclust")
        self.tbbounc = self.get_object("tbbounc")
#         self.tbcontrib = self.get_object("tbcontrib")
        self.tbdatabase = self.get_object("tbdatabase")
        self.tbkillbouncerdb = self.get_object("tbkillbouncerdb")
        self.nbmain = self.get_object("nbmain")
        self.lsStartText = self.get_object("lstartext")
        self.lsdetail = self.get_object("lsdetail")
        self.lsbody = self.get_object("lsbody")
        self.lsclust = self.get_object("lsclust")
        self.lsusers = self.get_object("lsusers")
        self.tvstart = self.get_object("tvstart")
        self.tvdetail = self.get_object("tvdetail")
        self.tvbody = self.get_object("tvbody")
        self.tbupdateldap = self.get_object("tbupdateldap")
        self.tbreload = self.get_object("tbreload")
        self.tbrestart = self.get_object("tbrestart")
        self.tbstop = self.get_object("tbstop")
        self.tbadd = self.get_object("tbadd")
        self.tbdel = self.get_object("tbdel")
        self.frmdbset = self.get_object("frmdbset")
        self.frmschemaset = self.get_object("frmschemaset")
        self.frmstbset = self.get_object("frmstbset")
        self.frmclustset = self.get_object("frmclustset")
        self.frmclustsetupgr = self.get_object("frmclustsetupgr")
        self.cbhost = self.get_object("cbhost")
        self.edport = self.get_object("edport")
        self.cbcluster = self.get_object("cbcluster")
        self.cbclusterEntry = self.get_object("cbcluster-entry")
        self.cbclusterupgrEntry = self.get_object("cbclusterupgr-entry")
        self.lbdbname = self.get_object("lbdbname")
        self.cbdbname = self.get_object("cbdbname")
        self.btinstall = self.get_object("btinstall")
        self.cbhostupgr = self.get_object("cbhostupgr")
        self.edportupgr = self.get_object("edportupgr")
        self.cbclusterupgr = self.get_object("cbclusterupgr")
        self.edpgversionupgr = self.get_object("edpgversionupgr")
        self.edpgwalsizeupgr = self.get_object("edpgwalsizeupgr")
        self.edpgblocksizeupgr = self.get_object("edpgblocksize")
        self.edpgwalblocksizeupgr = self.get_object("edpgwalblocksize")
        self.btupgrade = self.get_object("btupgrade")        
        self.tvLog = self.get_object("tvlog")
        self.tvSysLog = self.get_object("tvsyslog")
        self.swLog = self.get_object("swlog")
        self.swSysLog = self.get_object("swsyslog")
        self.cbstbmode = self.get_object("cbstbmode")
        self.edpgversion = self.get_object("edpgversion")
        self.edpgwalsize = self.get_object("edpgwalsize")
        self.edpgblocksize = self.get_object("edpgblocksize")
        self.edpgwalblocksize = self.get_object("edpgwalblocksize")
        self.chkinstsoft = self.get_object("chkinstsoft")
        self.chkpreinstsoft = self.get_object("chkpreinstsoft")
        self.chkschemainst = self.get_object("chkschemainst")
        self.lblogintemplate = self.get_object("lblogintemplate")
        self.cblogintemplate = self.get_object("cblogintemplate")
        self.dlgabout = self.get_object("dlgabout")
        self.edbname = self.get_object("edbname")
        self.edbencoding = self.get_object("edbencoding")
        self.edbtblsp = self.get_object("edbtblsp")
        self.edbadmin = self.get_object("edbadmin")
        self.btuseradd = self.get_object("btuseradd")
        self.edbtemplate = self.get_object("edbtemplate")
        self.ednetservice = self.get_object("ednetservice")
        self.edschname = self.get_object("edschname")
        self.edschowner = self.get_object("edschowner")
        self.edschownerEntry = self.get_object("edschowner-entry")
        self.edschtblspc = self.get_object("edschtblspc")
        self.edschencoding = self.get_object("edschencoding")
        self.edschsearchpath = self.get_object("edschsearchpath")
        self.swterm = self.get_object("swterm")
        
        self.mmsaveldap = self.get_object("mmsaveldap")
        self.mmdepldap = self.get_object("mmdepldap")
        self.mmadm = self.get_object("mmadm")
        self.mminst = self.get_object("mminst")
        self.mmabout = self.get_object("mmabout")
        self.mmquit = self.get_object("mmquit")
        self.mmusersadm = self.get_object("mmusersadm")
        self.mmgetdblist = self.get_object("mmgetdblist")
        self.mmuploadconf = self.get_object("mmuploadconf")
        self.mmtempladm = self.get_object("mmtempladm")
        
        self.rb1 = self.get_object("rb1")
        self.rb2 = self.get_object("rb2")
        
        
#====================================================

#---------------------------- Signals ++++++++++++++++++++++++++++++++
        
        self.fmain.connect("destroy", self.destroy)
        self.tbclust.connect("clicked", self.tbButtonToggled)
        self.tbbounc.connect("clicked", self.tbButtonToggled)
#         self.tbcontrib.connect("clicked", self.tbButtonToggled)
        self.tbdatabase.connect("clicked", self.tbButtonToggled)
        self.tbkillbouncerdb.connect("clicked", self.tbKillDBObjectClicked)
        self.tvstart.connect('cursor-changed', self.pgClusterChange)
        self.tvdetail.connect('cursor-changed', self.pgtvDetailChange)
        self.tvbody.connect('cursor-changed', self.tvBodyChange)
        self.tvbody.connect('button-press-event' , self.tvBodyMouseClick)
        self.tbupdateldap.connect("clicked", self.tbupdateldapClicked)
        self.tbreload.connect("clicked", self.tbreloadClicked)
        self.tbrestart.connect("clicked", self.tbrestartClicked)
        self.tbstop.connect("clicked", self.tbstopClicked)
        self.tbadd.connect("clicked", self.tbAddObjectClicked)
        self.tbdel.connect("clicked", self.tbDelObjectClicked)
        self.btinstall.connect("clicked", self.btInstallClicked)
        self.btupgrade.connect("clicked", self.btUpgradeClicked)
        self.btuseradd.connect("clicked", self.btUserAdd2ClusterClicked)
        self.tvLog.connect('size-allocate', self.tvLogChanged)
        self.tvSysLog.connect('size-allocate', self.tvSysLogChanged)
        self.chkschemainst.connect('toggled', self.chkSchemaInstChecked)
        self.edbname.connect('changed', self.edbNameChanged)
        self.edschname.connect('changed', self.edSchemaNameChanged)
        self.nbmain.connect_after('switch-page', self.nbMainPageSelected)
        
        self.mmsaveldap.connect("activate", self.mainmenuSave2LDAP)
        self.mmdepldap.connect("activate", self.mainmenuDrop2LDAP)
        self.mmadm.connect("activate", self.mainmenuAdmRules)
        self.mminst.connect("activate", self.mainmenuInstallRules)
        self.mmabout.connect("activate", self.mainmenuAboutForm)
        self.mmquit.connect("activate", self.mainmenuQuit)
        self.mmusersadm.connect("activate", self.mainmenuUsersAdm)
        self.mmgetdblist.connect("activate", self.mainmenuDrawDatabasesFromClusters)
        self.mmuploadconf.connect("activate", self.mainmenuUploadConfFilesBD)
        self.mmtempladm.connect("activate", self.mainmenuTemplateAdm)
        
        
#====================================================

#--------------------------- Object actions ---------------------------------


        cell = gtk.CellRendererText()
        col = gtk.TreeViewColumn(None, cell, text=0)
        self.tvstart.append_column(col)

        cell = gtk.CellRendererText()
        col = gtk.TreeViewColumn(None, cell, text=0)
        self.tvdetail.append_column(col)
        cell.connect('edited', self.editDetailPgBouncer, self.tvdetail.get_model())

        cell = gtk.CellRendererText()
        col = gtk.TreeViewColumn(None, cell, text=0)
        self.tvbody.append_column(col)
        cell = gtk.CellRendererText()
        cell.set_property('editable', False)
        col = gtk.TreeViewColumn(None, cell, text=1)
        self.tvbody.append_column(col)
        cell.connect('edited', self.editPgBouncer, self.tvbody.get_model())
        cell.connect('editing-started', self.editMultiText)
        self.tvbody.get_selection().set_mode(gtk.SELECTION_MULTIPLE)

        m = self.tvstart.get_model()
        m.set_sort_column_id(0,gtk.SORT_ASCENDING) 
        m = self.tvbody.get_model()
        m.set_sort_column_id(0,gtk.SORT_ASCENDING) 

        cell = gtk.CellRendererText()
        self.cbhost.pack_start(cell, True)
        self.cbhostupgr.pack_start(cell, True)
        self.cbhost.add_attribute(cell, 'text', 0)
        self.cbhostupgr.add_attribute(cell, 'text', 0)
        self.cbhost.connect("changed", self.cbHostChanged)
        self.cbhostupgr.connect("changed", self.cbHostChanged)
        m = self.cbhost.get_model()
        m.set_sort_column_id(0,gtk.SORT_ASCENDING) 

        
        cell = gtk.CellRendererText()
        self.cblogintemplate.pack_start(cell, True)
        self.cblogintemplate.add_attribute(cell, 'text', 0)          
        self.cblogintemplate.connect('changed', self.cbLoginTemplateChanged)
        
        cell = gtk.CellRendererText()
        self.cbcluster.set_text_column(0)
        self.cbclusterupgr.set_text_column(0)
        self.cbcluster.connect("changed", self.cbClusterChanged)
        m = self.cbcluster.get_model()
        m.set_sort_column_id(0,gtk.SORT_ASCENDING)         
        completion = gtk.EntryCompletion()
        completion.set_model(self.lsclust)
        completion.set_minimum_key_length(2)
        completion.set_text_column(0)
        self.cbcluster.child.set_completion(completion)
        
        self.tvLog.set_buffer(stdOut().bufferIO)
        self.tvSysLog.set_buffer(SysLog().bufferIO)

        cell = gtk.CellRendererText()
        self.cbstbmode.pack_start(cell, True)
        self.cbstbmode.add_attribute(cell, 'text', 0)  
        self.cbstbmode.append_text('transaction')
        self.cbstbmode.append_text('session')
        
        cell = gtk.CellRendererText()
        self.cbdbname.pack_start(cell, True)
        self.cbdbname.add_attribute(cell, 'text', 0)  
        m = self.cbdbname.get_model()
        m.set_sort_column_id(0,gtk.SORT_ASCENDING) 
        

        cell = gtk.CellRendererText()
        self.edschowner.set_text_column(0)
        completion = gtk.EntryCompletion()
        completion.set_model(self.lsusers)
        completion.set_minimum_key_length(2)
        completion.set_text_column(0)
        self.edschowner.child.set_completion(completion)
        self.drawCbUsers()
    
        
#======================================================================


    def tvBodyChange(self, treeview):
        self.checkBtLDAP()
    
    
    def tvBodyMouseClick(self, treeview, button):
        if button.type == gtk.gdk._2BUTTON_PRESS:
            m = self.tvbody.get_model()
            path, col = self.tvbody.get_cursor()
            dblink = m.get_value(m.get_iter(path), 1)
            if ',dc=rbc,dc=ru' in dblink:
                self.currentCluster = (self.currentCluster[0], dblink)
                self.clearBodyForms()
                self.drawObjectDetail(dblink)
    
    
    def checkBtLDAP(self, treeview = None):
        m, path = self.tvdetail.get_selection().get_selected_rows()
        self.tbrestart.set_sensitive(treeview != None and treeview == self.tvstart and (self.currentToolButtonPosition == "PgClusters" or self.currentToolButtonPosition == "PgBouncers"))
        self.tbstop.set_sensitive(treeview != None and treeview == self.tvstart and (self.currentToolButtonPosition == "PgClusters" or self.currentToolButtonPosition == "PgBouncers"))
        self.tbreload.set_sensitive(treeview != None and treeview == self.tvstart and (self.currentToolButtonPosition == "PgClusters" or self.currentToolButtonPosition == "PgBouncers"))
        for r in path:
            self.tbkillbouncerdb.set_sensitive(((m.get_value(m.get_iter(r), 0) != 'Базы данных') and (m.get_value(m.get_iter(r), 0) != 'Пользователи') and (m.get_value(m.get_iter(r), 0) != 'Общие настройки')) and ('cn=PgBouncers' in self.currentCluster[1]))
            self.tbadd.set_sensitive(((m.get_value(m.get_iter(r), 0) == 'Базы данных') or (m.get_value(m.get_iter(r), 0) == 'Пользователи')) and (not ('cn=PgClusters' in self.currentCluster[1]) or (('cn=PgClusters' in self.currentCluster[1]) and m.get_value(m.get_iter(r), 0) == 'Пользователи')) and (self.tvbody.get_selection().get_selected_rows()[1] != []))        
            self.tbdel.set_sensitive((m.get_value(m.get_iter(r), 0) != 'Базы данных') and (m.get_value(m.get_iter(r), 0) != 'Пользователи') and (m.get_value(m.get_iter(r), 0) != 'Библиотеки') and (m.get_value(m.get_iter(r), 0) != 'Skytools') and (m.get_value(m.get_iter(r), 0) != 'Общие настройки') and (m.get_value(m.get_iter(r), 0) != 'Файлы настроек БД') and (m.get_value(m.get_iter(r[0]), 0) != 'Файлы настроек БД'))
            self.mmuploadconf.set_sensitive(treeview != None and treeview == self.tvstart and self.currentToolButtonPosition == "PgClusters" or ((m.get_value(m.get_iter(r[0]), 0) == 'Файлы настроек БД') and (m.get_value(m.get_iter(r), 0) != 'Файлы настроек БД')))
        

    def tbKillDBObjectClicked(self, toolbutton):
        m, path = self.tvdetail.get_selection().get_selected_rows()
        curpath = m.get_path(m.iter_parent(m.get_iter(path[0])))
        for r in path:
            self.PgBouncerKillDB(m.get_value(m.get_iter(r),0))
                                 
        toolbutton.set_sensitive(False)
        

    def tbAddObjectClicked(self, toolbutton):
        m, path = self.tvbody.get_selection().get_selected_rows() 
        curpath = self.tvdetail.get_cursor()[0]
        for r in path:
            parentobj = self.tvdetail.get_model().get_value(self.tvdetail.get_model().get_iter(curpath), 0) 
            if parentobj == 'Базы данных':
                self.addNetService2PgBouncer(m.get_value(m.get_iter(r), 0), self.currentCluster[1])
#                 self.compareConfFileDB(m.get_value(m.get_iter(r), 0), self.currentCluster[1])                            Function autogenerated pg_hba access
            elif parentobj == 'Пользователи':
                for r in path:
                    self.addUsers2PgBouncer(m.get_value(m.get_iter(r), 0), self.currentCluster[1])
        self.drawBouncerDetail(self.currentCluster[1])
        self.tvdetail.expand_to_path(curpath)
        toolbutton.set_sensitive(False)


    def tbDelObjectClicked(self, toolbutton):
        m, path = self.tvdetail.get_selection().get_selected_rows()
        curpath = m.get_path(m.iter_parent(m.get_iter(path[0])))
        if self.tvbody.get_cursor()[0] != None:
            mpath = self.tvbody.get_cursor()[0]
            mmod = self.tvbody.get_model()
            self.deleteObjectFromPgBouncer(self.currentCluster[1], mmod.get_value(mmod.get_iter(mpath), 0))
        else:
            if 'cn=dbs,cn=' + self.currentCluster[0] + ',cn=PgClusters' in self.currentCluster[1]:
                self.deleteParentedObjectFromPgBouncers(self.currentCluster[1].split('cn=')[1].split(',')[0])
            self.deleteObjectFromPgBouncer(self.currentCluster[1])
        mpath = self.tvstart.get_cursor()[0]
        mmod = self.tvstart.get_model()
        self.currentCluster = (self.currentCluster[0],  mmod.get_value(mmod.get_iter(mpath), 1),)
        self.drawBouncerDetail(self.currentCluster[1])
        self.tvdetail.expand_to_path(curpath)
        toolbutton.set_sensitive(False)
    

    def tvLogChanged(self, widget, event, data=None):
        adj = self.swLog.get_vadjustment()
        adj.set_value( adj.upper - adj.page_size )


    def tvSysLogChanged(self, widget, event, data=None):
        adj = self.swSysLog.get_vadjustment()
        adj.set_value( adj.upper - adj.page_size )


    def btInstallClicked(self, widget):
        if self.currentToolButtonPosition == "PgClusters":
            self.threadedPgClusterInstall()
        elif self.currentToolButtonPosition == "PgBouncers":
            self.threadedPgBouncerInstall()
        elif self.currentToolButtonPosition == "PgDatabases":
            self.threadedPgDatabaseInstall()
    
    def btUpgradeClicked(self, widget):    
        if self.currentToolButtonPosition == "PgClusters":
            self.threadedPgClusterUpgrade()
    
    def btUserAdd2ClusterClicked(self, widget):
        self.nbmain.set_current_page(3)
        self.pgAddUser2Cluster()
        
        
    def pgAddUser2Cluster(self):
        pgb =  pgDatabaseAdm()
        self.loadPgClassFromLDAP(pgb, 'cn=' + self.cbcluster.get_active_text() + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if self.cbcluster.get_active_text() != '' and self.cbhost.get_active_text() != '':
            pgi = PgSchemaInstaller(pgb, self.getRealHostname(self.cbhost.get_active_text()), self.cbcluster.get_active_text(), self.cbdbname.get_active_text(), '', self.edschownerEntry.get_text(), self.edschtblspc.get_text(), self.edschencoding.get_text(), self.edschsearchpath.get_text())
            pgi.createOnlyUser()
            
        
    def threadedPgBouncerInstall(self):
        self.nbmain.set_current_page(3)
        gtk.threads_init()
        gtk.threads_enter()
        try:
            trdinst = ThreadPgBouncerInstall(self.getRealHostname(self.cbhost.get_active_text()), self.edport.get_text(), self.cbcluster.get_active_text(), self.cbstbmode.get_active_text(), self.chkinstsoft.get_active())
            trdinst.start()
        finally:
            gtk.threads_leave()
            trdinst = None


    def threadedPgClusterInstall(self):
        
#        pgi = PgClusterInstaller(self.cbhost.get_active_text(), self.edport.get_text(), self.cbcluster.get_active_text(), self.edpgversion.get_text())
#        if pgi.install() == 0:
#            pgi.registerPgClusterLDAP()
#        
#        
#        return
    
        self.nbmain.set_current_page(3)
        gtk.threads_init()
        gtk.threads_enter()
        try:
            trdinst = ThreadPgClusterInstall(self.getRealHostname(self.cbhost.get_active_text()), self.edport.get_text(), self.cbcluster.get_active_text(), self.edpgversion.get_text(), self.chkinstsoft.get_active(), {'walsize': self.edpgwalsize.get_text(), 'blocksize': self.edpgblocksize.get_text(), 'walblocksize': self.edpgwalblocksize.get_text()})
            trdinst.start()
        finally:
            gtk.threads_leave()
            trdinst = None

    def threadedPgClusterUpgrade(self):
        self.nbmain.set_current_page(3)
        gtk.threads_init()
        gtk.threads_enter()
        try:
            trdinst = ThreadPgClusterUpgrade(self.getRealHostname(self.cbhostupgr.get_active_text()), self.edportupgr.get_text(), self.cbclusterupgr.get_active_text(), self.edpgversionupgr.get_text(), self.chkpreinstsoft.get_active(), {'walsize': self.edpgwalsizeupgr.get_text(), 'blocksize': self.edpgblocksizeupgr.get_text(), 'walblocksize': self.edpgwalblocksizeupgr.get_text()})
            trdinst.start()
        finally:
            gtk.threads_leave()
            trdinst = None

            
    def threadedPgDatabaseInstall(self):
        self.nbmain.set_current_page(3)
        gtk.threads_init()
        gtk.threads_enter()
        try:
            if self.chkschemainst.get_active():
                trdinst = ThreadDbSchemaInstall(self.getRealHostname(self.cbhost.get_active_text()), self.cbcluster.get_active_text(), self.cbdbname.get_active_text(), self.edschname.get_text(), self.edschowner.get_active_text(), self.edschtblspc.get_text(), self.edschencoding.get_text(), self.edschsearchpath.get_text())
            else:
                trdinst = ThreadPgDatabaseInstall(self.getRealHostname(self.cbhost.get_active_text()), self.cbcluster.get_active_text(), self.edbname.get_text(), self.edbencoding.get_text(), self.edbtblsp.get_text(), self.edbtemplate.get_text(), self.ednetservice.get_text())
            trdinst.pgb = pgDatabaseAdm()
            self.loadPgClassFromLDAP(trdinst.pgb, 'cn=' + self.cbcluster.get_active_text() + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
            trdinst.start()
        finally:
            gtk.threads_leave()
            trdinst = None
        

    def threadedPgDatabaseSyncConfFiles(self, hostname, clsname, cnflname, cnfltext):
        self.nbmain.set_current_page(3)
        gtk.threads_init()
        gtk.threads_enter()
        try:
            trdinst = ThreadDbSyncConfFiles(self.getRealHostname(hostname), clsname, cnflname, cnfltext)
            trdinst.pgb = pgDatabaseAdm()
            self.loadPgClassFromLDAP(trdinst.pgb, 'cn=' + clsname + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
            trdinst.start()
        finally:
            gtk.threads_leave()
            trdinst = None

    def threadedSysLogMessages(self, clustername, tail):
        gtk.threads_init()
        gtk.threads_enter()
        try:
            self.SysLogSession = ThreadSysLogMessages(clustername, tail)
            self.SysLogSession.start()
        finally:
            gtk.threads_leave()


    def PgClusterRestart(self):
        self.nbmain.set_current_page(3)
        self.doPgClusterRestart(self.currentCluster[1])

    def PgClusterStop(self):
        self.nbmain.set_current_page(3)
        self.doPgClusterStop(self.currentCluster[1])       
        
    def doPgClusterRestart(self, clustername, command = ''):
        pgb = pgClusterAdm()
        self.loadPgClassFromLDAP(pgb, clustername)
        pgb.pgClusterName = self.currentCluster[0]
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)        
        if command == '':
            stdOut.write('Останавливаем приложение, если запущено...\n')
            pgb.pgRelatedCommand('stop')
            stdOut.write('База остановлена...\n')
            stdOut.write('Запускаем экземпляр приложения...\n')
            pgb.pgRelatedCommand('start')
            stdOut.write('Приложение запущено...\n')
        else:
            stdOut.write('Начинаем выполнение команды ' + command + '...\n')
            pgb.pgRelatedCommand(command)
            stdOut.write('Команда ' + command + ' выполнена успешно...\n')

    def doPgClusterStop(self, clustername, command = ''):
        pgb = pgClusterAdm()
        self.loadPgClassFromLDAP(pgb, clustername)
        pgb.pgClusterName = self.currentCluster[0]
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)        
        if command == '':
            stdOut.write('Останавливаем приложение, если запущено...\n')
            pgb.pgRelatedCommand('stop')
            stdOut.write('База остановлена...\n')
        else:
            stdOut.write('Начинаем выполнение команды ' + command + '...\n')
            pgb.pgRelatedCommand(command)
            stdOut.write('Команда ' + command + ' выполнена успешно...\n')

    def PgClusterReload(self):
        self.nbmain.set_current_page(3)
        self.doPgClusterReload(self.currentCluster[1])
        
    
    def doPgClusterReload(self, clustername):
        pgb = pgClusterAdm()
        self.loadPgClassFromLDAP(pgb, clustername)
        pgb.pgClusterName = self.currentCluster[0]
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)        
        pgb.pgRelatedCommand('reload')

    def PgBouncerKillDB(self, dbname):
        self.nbmain.set_current_page(3)
        self.doPgBouncerKillDB(self.currentClusterRootDN, dbname)

    def PgBouncerRestart(self):
        self.nbmain.set_current_page(3)
        self.doPgBouncerRestart(self.currentCluster[1])
        
    def PgBouncerStop(self):
        self.nbmain.set_current_page(3)
        self.doPgBouncerStop(self.currentCluster[1])
        
    def doPgBouncerKillDB(self, clustername, dbname):
        pgb = pgBouncerAdm()
        self.loadPgClassFromLDAP(pgb, clustername)
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)
        pgb.dbname = dbname
        stdOut.write('Убиваем процессы к базе данных ' + dbname + ' на баунсере ' + clustername + '...\n')
        pgb.pgRelatedCommand('killdb')             
        
    def doPgBouncerRestart(self, clustername, command = ''):
        pgb = pgBouncerAdm()
        self.loadPgClassFromLDAP(pgb, clustername)
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)
        if command == '':
            stdOut.write('Останавливаем приложение, если запущено...\n')
            pgb.pgRelatedCommand('stop')
            stdOut.write('Баунсер остановлен...\n')
            stdOut.write('Запускаем экземпляр приложения...\n')
            pgb.pgRelatedCommand('start')
            stdOut.write('Приложение запущено...\n')
        else:
            stdOut.write('Начинаем выполнение команды ' + command + '...\n')
            pgb.pgRelatedCommand(command)
            stdOut.write('Команда ' + command + ' выполнена успешно...\n')
        
    def doPgBouncerStop(self, clustername, command = ''):
        pgb = pgBouncerAdm()
        self.loadPgClassFromLDAP(pgb, clustername)
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)
        if command == '':
            stdOut.write('Останавливаем приложение, если запущено...\n')
            pgb.pgRelatedCommand('stop')
            stdOut.write('Баунсер остановлен...\n')
        else:
            stdOut.write('Начинаем выполнение команды ' + command + '...\n')
            pgb.pgRelatedCommand(command)
            stdOut.write('Команда ' + command + ' выполнена успешно...\n')
        
    def PgBouncerReload(self):
        self.nbmain.set_current_page(3)
        self.doPgBouncerReload(self.currentCluster[1])
        
    
    def doPgBouncerReload(self, clustername):
        pgb = pgBouncerAdm()
        self.loadPgClassFromLDAP(pgb, clustername)
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)        
        pgb.pgRelatedCommand('reload')
        

    def update2LDAP(self):
        if self.ldif2LDAP != {}:
            try:
                if any('cn=PgClusters' or 'cn=ConfTemplates' in item for item in self.ldif2LDAP.keys()):
                    login, passw = dlgLoginPasswInput.AuthFromKeyring('pgadmin', 'uid=pgadmin,ou=Users,dc=rbc,dc=ru')
                    self.ldap.bind_s(login, passw)
                elif any('cn=PgBouncers' in item for item in self.ldif2LDAP.keys()):
#                    self.ldap.bind_s(ldap_auth_pgbouncadm['login'],ldap_auth_pgbouncadm['password'])
                    login, passw = dlgLoginPasswInput.AuthFromKeyring('pgbounceradmin', 'uid=pgbounceradmin,ou=Users,dc=rbc,dc=ru')
                    self.ldap.bind_s(login, passw)
                elif any('cn=PgNetServices' in item for item in self.ldif2LDAP.keys()):
                    login, passw = dlgLoginPasswInput.AuthFromKeyring('pgnetadmin', 'uid=pgnetadmin,ou=Users,dc=rbc,dc=ru')
                    self.ldap.bind_s(login, passw)
                for rcn in self.ldif2LDAP:
                    for rls in self.ldif2LDAP[rcn]:
                        if rls[1] == 'cn':
                            self.ldap.rename_s(rcn, 'cn=' + rls[2])
                        else: 
                            self.ldap.modify_s(rcn, [rls]) 
                
            except Exception, e:
                stdOut.write('Ошибка обновления записи в LDAP\n' + str(e) + '\n')
            finally:
                self.ldap.bind_s('','')
                
    
    def editDetailPgBouncer(self, cell, path, new_text, user_data):
        liststore = user_data
        liststore[path][0] = new_text
        if not self.currentCluster[1] in self.ldif2LDAP.keys():
            self.ldif2LDAP[self.currentCluster[1]] = [(ldap.MOD_REPLACE, 'cn', liststore[path][0],)]
        else:
            self.ldif2LDAP[self.currentCluster[1]].append((ldap.MOD_REPLACE, 'cn', liststore[path][0],))
        self.tbupdateldap.set_sensitive(True)
        
        
    def editMultiText(self, cell, editable, path):
        liststore = self.tvbody.get_model() 
        if '\n' in editable.get_text():
            
            self.editPgBouncer(cell, path, dlgMultiLineText.doEdit(self, editable.get_text()), liststore)
            self.fmain.set_focus(self.edbencoding)
            
#            liststore = self.tvbody.get_model() 
#            liststore[path][1] = dlgMultiLineText.doEdit(self, editable.get_text())
            if not self.currentCluster[1] in self.ldif2LDAP.keys():
                self.ldif2LDAP[self.currentCluster[1]] = [(ldap.MOD_REPLACE, liststore[path][0], liststore[path][1],)]
            else:
                self.ldif2LDAP[self.currentCluster[1]].append((ldap.MOD_REPLACE, liststore[path][0], liststore[path][1],))
            self.tbupdateldap.set_sensitive(True)


    def editPgBouncer(self, cell, path, new_text, user_data):
        liststore = user_data
        liststore[path][1] = new_text
        apath = self.tvdetail.get_cursor()[0]
        if len(apath) == 3:
            if 'cn=confiles' in self.currentCluster[1]:
                self.ldif2LDAP['cn=' + liststore[path][0] + ',' + self.currentCluster[1]] = [(ldap.MOD_REPLACE, 'pgConfParamValue', liststore[path][1],)]
            elif 'cn=pgqueues' in self.currentCluster[1]:
                self.ldif2LDAP[self.currentCluster[1]] = [(ldap.MOD_REPLACE, 'pgbConfigSettings', liststore[path][1],)]
        else:
            if not self.currentCluster[1] in self.ldif2LDAP.keys():
                self.ldif2LDAP[self.currentCluster[1]] = [(ldap.MOD_REPLACE, liststore[path][0], liststore[path][1],)]
            else:
                self.ldif2LDAP[self.currentCluster[1]].append((ldap.MOD_REPLACE, liststore[path][0], liststore[path][1],))
        self.tbupdateldap.set_sensitive(True)
  

    def pgClusterChange(self, subject):
        path = subject.get_cursor()[0]
        try:
            m = subject.get_model()
            pgclustername = m.get_value(m.get_iter(path), 0)
            self.currentCluster = (pgclustername,  m.get_value(m.get_iter(path), 1),)
            self.currentClusterRootDN = m.get_value(m.get_iter(path), 1)
            self.drawBouncerDetail(self.currentCluster[1])
            self.tvdetail.set_cursor((0,))
            for obj in self.swterm:
                if obj.__class__ == cVTerminal:
                    obj.destroy()
            self.drawSysLogMessages(self.currentCluster[0])

        except Exception, e:
                sys.stdout.write(str(e) + '\n')
        finally:
            self.checkBtLDAP(subject)

            
    def MainTemplateAdm(self):
        confrmldap = self.getObjectDetailTreeFromLDAP('cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru',['cn'], ldap.SCOPE_ONELEVEL)
        if not confrmldap is None:
            self.clearAllForms()
            self.lsStartText.append(['Шаблоны конфигураций','cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru'])
            m = self.tvstart.get_model()
            self.currentCluster = ('ConfTemplates',  m.get_value(m.get_iter((0,)), 1),)
            self.tvstart.set_cursor(0)
            for dn, rattr in confrmldap:
                self.drawTemplates(rattr['cn'])
    

    def doUploadConfFilesBD(self, clustername, confile = ('pg_hba','postgresql','stdb_recovery')):
        for cnfl in confile:
            confrmldap = self.getObjectDetailFromLDAP('cn=' + cnfl + ',cn=confiles,cn=' + clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
            if not confrmldap is None: 
                for dn, rattr in confrmldap:
                    self.syncConfFile(''.join(rattr['pgContribName']), ''.join(rattr['pgbConfigSettings']), clustername)


    def syncConfFile(self, cnflname, cnftext, clustername):
        clscnf = self.getBouncerDetailFromLDAP('cn=' + clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        if not clscnf is None:
            for dn, rattr in clscnf: 
                self.threadedPgDatabaseSyncConfFiles(''.join(rattr['dbaHostName']), clustername, cnflname, cnftext)
        

    def doUpdate2LDAP(self):
        try:
            self.update2LDAP()
        finally:
            self.LDAPpdated()


    def LDAPpdated(self):
        self.ldif2LDAP = {}
        self.tbupdateldap.set_sensitive(False)

        
    def pgtvDetailChange(self, subject):
        self.clearBodyForms()
        self.tvbody.get_columns()[1].get_cell_renderers()[0].set_property('editable', False)
        self.tvdetail.get_columns()[0].get_cell_renderers()[0].set_property('editable', False)
        path = subject.get_cursor()[0]
        try:
            m = subject.get_model()
            objname = m.get_value(m.get_iter(path), 0)
            objtype = m.get_value(m.get_iter((path[0],)), 0)

            mpath = self.tvstart.get_cursor()[0]
            mmod = self.tvstart.get_model()
            self.currentCluster = (self.currentCluster[0],  mmod.get_value(mmod.get_iter(mpath), 1),)

            if self.currentCluster[0] == 'Шаблоны конфигураций':
                self.tvbody.get_columns()[1].get_cell_renderers()[0].set_property('editable', True)
                if len(path) == 1:
                    self.drawBouncerDetailTree('cn=' + objname + ',' + self.currentCluster[1])
                    self.currentCluster = (self.currentCluster[0], 'cn=' + objname + ',' + self.currentCluster[1])
                elif len(path) == 2:
                    self.drawBouncerDetailTree('cn=' + objname + ',cn=' + objtype + ',' + self.currentCluster[1])
                    self.currentCluster = (self.currentCluster[0], 'cn=' + objname + ',cn=' + objtype + ',' + self.currentCluster[1])
            else:
                if len(path) == 1:
                    if objname == 'Общие настройки':
                        self.tvbody.get_columns()[1].get_cell_renderers()[0].set_property('editable', True)
                        self.drawBouncerDetailTree(self.currentCluster[1])
                    elif objname == 'Базы данных' and (not 'cn=PgClusters' in self.currentCluster[1]):
                        self.drawNetServicesTree()
                    elif objname == 'Пользователи':
                        self.drawUsersTree()
                elif len(path) == 2:
                    self.tvbody.get_columns()[1].get_cell_renderers()[0].set_property('editable', True)
                    self.tvdetail.get_columns()[0].get_cell_renderers()[0].set_property('editable', True)
                    if 'cn=PgClusters' in self.currentCluster[1]:
                        if self.pgClusterDetailType[objtype] == 'contribs':
                            objname = objname.split('{')[0]
                        self.drawObjectDetail('cn=' + objname + ',cn=' + self.pgClusterDetailType[objtype] + ',' + self.currentCluster[1])
                        self.currentCluster = (self.currentCluster[0], 'cn=' + objname + ',cn=' + self.pgClusterDetailType[objtype] + ',' + self.currentCluster[1])
                    elif 'cn=PgBouncers' in self.currentCluster[1]:
                        self.drawObjectDetail('cn=' + objname + ',cn=' + self.pgBouncerDetailType[objtype] + ',' + self.currentCluster[1])
                        self.currentCluster = (self.currentCluster[0], 'cn=' + objname + ',cn=' + self.pgBouncerDetailType[objtype] + ',' + self.currentCluster[1])                
                elif len(path) == 3:
                    self.tvbody.get_columns()[1].get_cell_renderers()[0].set_property('editable', True)
                    if objtype == 'Файлы настроек БД':
                        if objname in self.pgClusterDetailType.values():
                            confrmldap = self.getPostgreSQLConfFromLDAP(self.currentCluster[1])
                            if not confrmldap is None: 
                                groupattr = self.pgClusterDetailType.keys()[self.pgClusterDetailType.values().index(objname)] 
                                if groupattr in confrmldap.keys():
                                    self.drawObjectDetailTree('cn=' + groupattr + ',cn=postgresql,cn=confiles,' + self.currentCluster[1], ['cn','pgConfParamValue'], ldap.SCOPE_ONELEVEL)
                                    self.currentCluster = (self.currentCluster[0], 'cn=' + groupattr + ',cn=postgresql,cn=confiles,' + self.currentCluster[1])
                    elif objtype == 'Базы данных':
                        self.drawObjectDetailTree('cn=' + objname + ',cn=pgqueues,cn=' + m.get_value(m.get_iter((path[0], path[1], )), 0) + ',cn=dbs,' + self.currentCluster[1], ['cn','pgbConfigSettings'])
                        self.currentCluster = (self.currentCluster[0], 'cn=' + objname + ',cn=pgqueues,cn=' + m.get_value(m.get_iter((path[0], path[1], )), 0) + ',cn=dbs,' + self.currentCluster[1])
        except Exception, e:
                sys.stdout.write(str(e) + '\n')
        finally:
            self.checkBtLDAP()


    def untoggleAllButtons(self, nonToggledItem):
        self.currentToolButtonPosition = nonToggledItem.get_label()
        for tb in self.tbmain:
            if isinstance(tb, gtk.ToggleToolButton):
                if tb.get_active() and (tb != nonToggledItem):
                    tb.set_active(False)
                 
                 
    def tbupdateldapClicked(self, toolbutton):
        self.doUpdate2LDAP()

    
    def chkSchemaInstChecked(self, togglebutton):
        self.frmschemaset.set_visible(togglebutton.get_active())
        self.lbdbname.set_visible(togglebutton.get_active())
        self.cbdbname.set_visible(togglebutton.get_active())
        self.edport.set_sensitive(togglebutton.get_active())
        self.lblogintemplate.set_visible(togglebutton.get_active())
        self.cblogintemplate.set_visible(togglebutton.get_active())
        self.frmdbset.set_visible(not togglebutton.get_active())
        

    def cbClusterChanged(self, combobox):
        self.doDrawDbNames(combobox.get_active_text())
        
    def cbLoginTemplateChanged(self, combobox):
        pgb = pgDatabaseAdm()
        self.loadPgClassFromLDAP(pgb, 'cn=' + self.cbcluster.get_active_text() + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
        pgb.dbaHostName = self.getRealHostname(pgb.dbaHostName)
        pgb.pgClusterName = self.cbcluster.get_active_text()
        rtr = pgb.pgGetUserConfig(combobox.get_active_text())
        if rtr != {}:
            if 'client_encoding' in rtr.keys():
                self.edschencoding.set_text(rtr['client_encoding'])
            if 'default_tablespace' in rtr.keys():
                self.edschtblspc.set_text(rtr['default_tablespace'])
            if 'search_path' in rtr.keys():
                self.edschsearchpath.set_text(rtr['search_path'])
                
    
    def cbHostChanged(self, combobox):
        if self.currentToolButtonPosition == 'PgDatabases':
            self.cbcluster.set_active(-1)
            self.cbclusterEntry.set_text('')
            m = self.cbcluster.get_model()
            self.cbcluster.set_model(None)
            m.clear()
            self.cbcluster.set_model(m)
            frmldap = self.getClustersFromLDAP(combobox.get_active_text())
            if not frmldap is None:
                for dn, rattr in frmldap:
                    self.cbcluster.append_text(' '.join(rattr['cn']))
        elif (self.currentToolButtonPosition == 'PgClusters') and (self.nbmain.get_current_page() == 2):
            self.cbclusterupgr.set_active(-1)
            self.cbclusterupgrEntry.set_text('')
            m = self.cbclusterupgr.get_model()
            self.cbclusterupgr.set_model(None)
            m.clear()
            self.cbclusterupgr.set_model(m)
            frmldap = self.getClustersFromLDAP(combobox.get_active_text())
            if not frmldap is None:
                for dn, rattr in frmldap:
                    self.cbclusterupgr.append_text(' '.join(rattr['cn']))
            
        
    def drawCbUsers(self):    
        self.edschowner.set_active(-1)
        self.edschownerEntry.set_text('')
        m = self.edschowner.get_model()
        self.edschowner.set_model(None)
        m.clear()
        self.edschowner.set_model(m)
        frmldap = self.getUsersFromLDAP()
        if not frmldap is None:
            for dn, rattr in frmldap:
                self.edschowner.append_text(' '.join(rattr['cn']))
    
    
    def drawSysLogMessages(self, clustername):
        if not self.SysLogSession is None:
            self.SysLogSession.sshclient.close()
        buf = self.tvSysLog.get_buffer()
        buf.set_text('')
        self.threadedSysLogMessages(clustername, 'f')

    
    def edSchemaNameChanged(self, entry):
        self.edschsearchpath.set_text(entry.get_text() + ',public')
    
    
    def edbNameChanged(self, entry):
        self.edbtblsp.set_text(entry.get_text() + '_data')
        self.ednetservice.set_text('ns_' + entry.get_text())
        

    def tbreloadClicked(self, toolbutton):
        if self.currentToolButtonPosition == "PgClusters":
            self.PgClusterReload()
        elif self.currentToolButtonPosition == "PgBouncers":
            self.PgBouncerReload()

    def tbrestartClicked(self, toolbutton):
        if self.currentToolButtonPosition == "PgClusters":
            self.PgClusterRestart()
        elif self.currentToolButtonPosition == "PgBouncers":
            self.PgBouncerRestart()       

    def tbstopClicked(self, toolbutton):
        if self.currentToolButtonPosition == "PgClusters":
            self.PgClusterStop()
        elif self.currentToolButtonPosition == "PgBouncers":
            self.PgBouncerStop()  

    def tbButtonToggled(self, toolbutton):
#         if toolbutton.get_active():
        self.toggledButtonState(toolbutton.get_label())
#         self.untoggleAllButtons(toolbutton)
            

    def nbMainPageSelected(self, nb, page, pagenum):
        try:
            if pagenum == 4:
                if len(self.swterm) == 0:
                    frmldap = self.getObjectDetailFromLDAP(self.currentCluster[1])
                    if not frmldap is None:
                        for dn, rattr in frmldap: 
                            login, passw = dlgLoginPasswInput.AuthFromKeyring(''.join(rattr['dbaHostName']))
                            self.swterm.add(cVTerminal(self.getRealHostname(''.join(rattr['dbaHostName'])), login))
        except Exception, e:
            stdOut.write('Ошибка открытия окна терминала\n' + str(e) + '\n')            
        

    def toggledButtonState(self, toolbutton):
        self.currentToolButtonPosition = toolbutton
        if toolbutton == "PgClusters":
            self.doCluster()
        elif toolbutton == "PgBouncers":
            self.doBouncer()
        elif toolbutton == "PgDatabases":
            self.doDatabase()
        self.realignInstallPage(toolbutton)


    def realignInstallPage(self, activePage):
        self.clearInstForms()
        self.frmclustset.set_visible(activePage == "PgClusters")
        self.frmclustsetupgr.set_visible(activePage == "PgClusters")
        self.frmdbset.set_visible(activePage == "PgDatabases")
        self.frmstbset.set_visible(activePage == "PgBouncers")
        self.frmschemaset.set_visible(False)
        self.chkpreinstsoft.set_visible(activePage == "PgClusters")
        self.chkschemainst.set_visible(activePage == "PgDatabases")
        self.chkinstsoft.set_visible(activePage == "PgClusters" or activePage == "PgBouncers")
        self.edport.set_sensitive(not activePage == "PgDatabases")
        
        
        if activePage == "PgClusters":
            self.drawInstPgCluster()
#            self.frmclustset.set_visible(True)
#            self.frmdbset.set_visible(False)
#            self.frmstbset.set_visible(False)
#            self.frmschemaset.set_visible(False)
#            self.chkupdatesoft.set_visible(True)
#            self.chkschemainst.set_visible(False)
#            self.chkregldap.set_visible(True)
        elif activePage == "PgBouncers":
            self.drawInstPgBouncer()
#            self.frmclustset.set_visible(False)
#            self.frmdbset.set_visible(False)
#            self.frmstbset.set_visible(True)
#            self.frmschemaset.set_visible(False)
#            self.chkupdatesoft.set_visible(False)
#            self.chkschemainst.set_visible(False)
#            self.chkregldap.set_visible(False)
        elif activePage == "PgDatabases":
            self.drawInstDatabase()
#            self.frmclustset.set_visible(False)
#            self.frmdbset.set_visible(True)
#            self.frmstbset.set_visible(False)
#            self.frmschemaset.set_visible(False)
#            self.chkupdatesoft.set_visible(False)
#            self.chkschemainst.set_visible(True)
#            self.chkregldap.set_visible(False)


    def deleteParentedObjectFromPgBouncers(self, dbname):
        bncfrmldap = self.getBouncersFromLDAP()
        if not bncfrmldap is None:
            for dn, rattr in bncfrmldap:                
                bdbfrmldap = self.getBouncerDatabasesFromLDAP(dn)
                if not bdbfrmldap is None:
                    for dbdn, dbrattr in bdbfrmldap:
                        bdbdetfrmldap = self.getObjectDetailFromLDAP(dbdn)
                        if not bdbdetfrmldap is None:
                            for dbdetdn, dbdetrattr in bdbdetfrmldap:
                                if ('dbaDBLink' in dbdetrattr.keys()) and (''.join(dbdetrattr['dbaDBLink']) != ''):
                                    nsfrmldap = self.getObjectDetailFromLDAP(''.join(dbdetrattr['dbaDBLink']))
                                    if not nsfrmldap is None:
                                        for nsdn, nsrattr in nsfrmldap:
                                            if (''.join(nsrattr['pgDBName']) != '') and (''.join(nsrattr['pgDBName']) == dbname):
                                                self.deleteObjectFromPgBouncer(dbdn)
                                                stdOut.write('Удаляем базу ' + str(dbdn) + '\nНЕ ЗАБУДЬТЕ ПЕРЕЗАПУСТИТЬ ' + str(dn) + '\n')
                                else:
                                    if ''.join(dbdetrattr['pgDBName']) == dbname:
                                        self.deleteObjectFromPgBouncer(dbdn)
                                        stdOut.write('Удаляем базу ' + str(dbdn) + '\nНЕ ЗАБУДЬТЕ ПЕРЕЗАПУСТИТЬ ' + str(dn) + '\n')


    def deleteObjectFromPgBouncer(self, basedn, cndeleted = ''):
        self.deleteFromLDAP(basedn, cndeleted)


    def addDblink2PgCluster(self, srvname, dnpgcluster): 
        ldif2LDAP = self.prepareDbnameAdd2LDAP(srvname, 'cn=' + srvname + ',cn=PgNetServices,cn=PgContext,dc=rbc,dc=ru')
        self.add2LDAP('cn=' + srvname + ',cn=dbs,' + dnpgcluster, ldif2LDAP)


    def addNetService2PgBouncer(self, srvname, dnpgcluster):
        ldif2LDAP = self.prepareDBLinksAdd2LDAP(srvname, 'cn=' + srvname + ',cn=PgNetServices,cn=PgContext,dc=rbc,dc=ru')
        self.add2LDAP('cn=' + srvname + ',cn=dblinks,' + dnpgcluster, ldif2LDAP)


    def addUsers2PgBouncer(self, srvname, dnpgcluster):
        ldif2LDAP = self.prepareAliasAdd2LDAP(srvname, 'uid=' + srvname + ',ou=Users,dc=rbc,dc=ru')
        self.add2LDAP('cn=' + srvname + ',cn=users,' + dnpgcluster, ldif2LDAP)
        
        
    def prepareDbnameAdd2LDAP(self, aliasname, aliasdn):
        rtr = []
        rtr.append(('objectClass', ['top', 'rbcPgContribsList', 'rbcPgDataBase'],))
        rtr.append(('pgDBClobalID', self.searchMaxCntFromLDAP('cn=PgClusters,cn=PgContext,dc=rbc,dc=ru', 'pgDBClobalID') + 1))        
        return rtr
    
    def prepareDeleteFromLDAP(self, basedn, cndeleted):
        self.ldif2LDAP = {}
        self.ldif2LDAP[basedn] = [(ldap.MOD_DELETE, cndeleted, None)]

    def prepareDBLinksAdd2LDAP(self, aliasname, aliasdn):
        rtr = []
        rattr = None
        dtlfrmldap = self.getObjectDetailFromLDAP(aliasdn)
        if not dtlfrmldap is None:
            dn, rattr = dtlfrmldap[0]
                
        rtr.append(('objectClass', ['top', 'rbcContainer', 'rbcPgNetService'],))
        if not rattr is None and 'dbaHostName' in rattr.keys():
            rtr.append(('dbaHostName', ' '.join(rattr['dbaHostName'])))
        else:
            rtr.append(('dbaHostName', ' '))
        if not rattr is None and 'dbaPort' in rattr.keys():
            rtr.append(('dbaPort', ' '.join(rattr['dbaPort'])))
        else:
            rtr.append(('dbaPort', '1234'))
        if not rattr is None and 'pgConnectParams' in rattr.keys():
            rtr.append(('pgConnectParams', ' '.join(rattr['pgConnectParams'])))
        else:
            rtr.append(('pgConnectParams', ' '))
        if not rattr is None and 'pgDBName' in rattr.keys():
            rtr.append(('pgDBName', ' '.join(rattr['pgDBName'])))
        else:
            rtr.append(('pgDBName', ' '))
        rtr.append(('dbaDBLink', aliasdn,))
        rtr.append(('cn', aliasname,))
        return rtr
    
    
    def prepareAliasAdd2LDAP(self, aliasname, aliasdn):
        rtr = []
        rtr.append(('objectClass', ['top', 'alias', 'extensibleObject'],))
        rtr.append(('aliasedObjectName', aliasdn,))
        rtr.append(('cn', aliasname,))
        return rtr


    def add2LDAP(self, basedn, ldif2LDAP):
        if ldif2LDAP != []:
            try:
                if any('cn=PgClusters' in item for item in self.currentCluster) and any('cn=dbs' in item for item in self.currentCluster):
                    login, passw = dlgLoginPasswInput.AuthFromKeyring('pgregdbs', 'uid=pgregdbs,ou=Users,dc=rbc,dc=ru')
                    self.ldap.bind_s(login, passw)
                elif any('cn=PgClusters' in item for item in self.currentCluster):
                    login, passw = dlgLoginPasswInput.AuthFromKeyring('pgadmin', 'uid=pgadmin,ou=Users,dc=rbc,dc=ru')
                    self.ldap.bind_s(login, passw)
                elif any('cn=PgBouncers' in item for item in self.currentCluster):
                    login, passw = dlgLoginPasswInput.AuthFromKeyring('pgbounceradmin', 'uid=pgbounceradmin,ou=Users,dc=rbc,dc=ru')
                    self.ldap.bind_s(login, passw)
                self.ldap.add_s(basedn, ldif2LDAP) 
            except Exception, e:
                stdOut.write('ERROR: ' + str(e) + '\nAdd to LDAP dn: ' + str(basedn) + '\nLDIF: ' + str(ldif2LDAP) + '\nlogin: ' + str(login) + ' passw: ' + str(passw[:1]) + '****' + str(passw[-1:]) + '\n')
            finally:
                self.ldap.bind_s('','')
        
        
    def deleteFromLDAP(self, basedn, cndeleted):
        try:
            if any('cn=PgClusters' in item for item in self.currentCluster):
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgadmin', 'uid=pgadmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
            elif any('cn=PgBouncers' in item for item in self.currentCluster):
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgbounceradmin', 'uid=pgbounceradmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                
            if any('cn=dbs' in item for item in self.currentCluster) and any('cn=PgClusters' in item for item in self.currentCluster):
                self.ldap.delete_s('cn=contribs,' + basedn)
                
            if cndeleted == '':
                self.ldap.delete_s(basedn)
            else:
                self.prepareDeleteFromLDAP(basedn, cndeleted)
                if self.ldif2LDAP != {}:
                    self.ldap.modify_s(basedn, self.ldif2LDAP[basedn])
        except Exception, e:
            stdOut.write('ERROR: ' + str(e) + '\nDelete from LDAP dn: ' + str(basedn) + '\nLDIF: ' + str(self.ldif2LDAP[basedn]) + '\nlogin: ' + str(login) + ' passw: ' + str(passw[:1]) + '****' + str(passw[-1:]) + '\n')
        finally:
            self.ldap.bind_s('','')
        
        

    def doCluster(self):
        self.drawClustersTree()
    
    def doBouncer(self):
        self.drawBouncersTree()
      
    def doDatabase(self):
        self.drawDatabaseTree()

    def drawSimpleComponents(self):
        frmldap = self.getHostsFromLDAP()
        if not frmldap is None:
            for dn, rattr in frmldap:
                self.cbhost.append_text(' '.join(rattr['cn']))
        frmldap = self.getClustersFromLDAP()
        if not frmldap is None:
            for dn, rattr in frmldap:
                self.cbcluster.append_text(' '.join(rattr['cn']))


    def drawDatabaseComponents(self):
        self.doDrawDbNames(self.cbcluster.get_active_text())
        
        
    def doDrawDbNames(self, clustername):
        if (clustername != '') and self.currentToolButtonPosition == 'PgDatabases':
            self.cbdbname.set_active(-1)
            m = self.cbdbname.get_model()
            self.cbdbname.set_model(None)
            m.clear()
            self.cbdbname.set_model(m)
            frmldap = self.getDatabasesFromLDAP(clustername)
            if not frmldap is None:
                for dn, rattr in frmldap:
                    self.cbdbname.append_text(' '.join(rattr['cn']))
            
            self.cblogintemplate.set_active(-1)
            m = self.cblogintemplate.get_model()
            self.cblogintemplate.set_model(None)
            m.clear()
            self.cblogintemplate.set_model(m)
            frmldap = self.getBouncerUsersFromLDAP('cn=' + clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
            if not frmldap is None:
                for dn, rattr in frmldap:
                    self.cblogintemplate.append_text(' '.join(rattr['cn']))

      
    def drawInstPgCluster(self):
        self.drawSimpleComponents()
        
      
    def drawInstPgBouncer(self):
        self.drawSimpleComponents()
        

    def drawInstDatabase(self):
        self.drawSimpleComponents()
        self.drawDatabaseComponents()
    
        
    def drawObjectDetail(self, cncontext):
        dtlfrmldap = self.getObjectDetailFromLDAP(cncontext)
        if not dtlfrmldap is None:
            for dn, rattr in dtlfrmldap:
                for attr in rattr:
                    if not attr in ('objectClass','cn',):
                        self.lsbody.append([attr, ', '.join(rattr[attr])])


    def drawObjectDetailTree(self, cncontext, attrvals, scope=ldap.SCOPE_BASE):
        dtlfrmldap = self.getObjectDetailTreeFromLDAP(cncontext, attrvals, scope)
        if not dtlfrmldap is None:
            for dn, rattr in dtlfrmldap:
                for attr in rattr:
                    if not attr in ('objectClass','cn',):
                        if attr == 'pgConfParamValue':
                            self.lsbody.append([''.join(rattr['cn']), ', '.join(rattr[attr])])
                        else:
                            self.lsbody.append([attr, ', '.join(rattr[attr])])

        
    def drawClustersTree(self):
        self.clearAllForms()
        clstfrmldap = self.getClustersFromLDAP()
        if not clstfrmldap is None:
            for dn, rattr in clstfrmldap:
                self.lsStartText.append([' '.join(rattr['cn']),dn])
        

    
    def drawBouncerDetailTree(self, pgclustername):
        attrbounc = self.getBouncerDetailFromLDAP(pgclustername)
        if not attrbounc is None:
            for dn, rattr in attrbounc:
                for attr in rattr:
                    if not attr in ('objectClass','cn',):
                        self.lsbody.append([attr, '\n'.join(rattr[attr])])
                    
        
    def drawBouncerDetail(self, pgclustername):
        parentContrib = None
        parentSkytools = None
        parentConfFilesBD = None
        parentPostgreSQLConf = None
        parentQueues = None
        self.lsdetail.clear()
        self.lsbody.clear()
        if ('cn=PgClusters' in self.currentCluster[1]) or ('cn=PgBouncers' in self.currentCluster[1]):
            self.lsdetail.append(None,['Общие настройки'])
            parentDB = self.lsdetail.append(None,['Базы данных'])
            parentUsr = self.lsdetail.append(None,['Пользователи'])
        if 'cn=PgClusters' in self.currentCluster[1]:
            parentConfFilesBD = self.lsdetail.append(None,['Файлы настроек БД'])
            parentContrib = self.lsdetail.append(None,['Библиотеки'])
            parentSkytools = self.lsdetail.append(None,['Skytools'])
        if pgclustername != None:
            if 'cn=PgClusters' in self.currentCluster[1]:
                dbfrmldap = self.getClusterDatabasesFromLDAP(pgclustername)
            elif 'cn=PgBouncers' in self.currentCluster[1]:
                dbfrmldap = self.getBouncerDatabasesFromLDAP(pgclustername)
            if not dbfrmldap is None: 
                for dn, rattr in dbfrmldap:
                    parentQueues = self.lsdetail.append(parentDB,rattr['cn'])
                    qfrmldap = self.getQueuesDatabaseFromLDAP(pgclustername, ''.join(rattr['cn']))
                    if not qfrmldap is None: 
                        for dn, rattr in qfrmldap:
                            self.lsdetail.append(parentQueues, rattr['cn'])

            usrfrmldap = self.getBouncerUsersFromLDAP(pgclustername)
            if not usrfrmldap is None: 
                for dn, rattr in usrfrmldap:
                    self.lsdetail.append(parentUsr,rattr['cn'])
            if not parentContrib is None:
                contribfrmldap = self.getClusterContribsFromLDAP(pgclustername)
                if not contribfrmldap is None: 
                    for dn, rattr in contribfrmldap:
                        for attr in rattr['pgContribName']:
                            self.lsdetail.append(parentContrib, [attr])
            if not parentSkytools is None:
                skytoolsfrmldap = self.getClusterSkytoolsFromLDAP(pgclustername)
                if not skytoolsfrmldap is None: 
                    for dn, rattr in skytoolsfrmldap:
                        self.lsdetail.append(parentSkytools,rattr['cn'])
            if not parentConfFilesBD is None:
                confrmldap = self.getClusterConfFilesFromLDAP(pgclustername)
                if not confrmldap is None: 
                    for dn, rattr in confrmldap:
                        if 'postgresql' in rattr['cn']:
                            parentPostgreSQLConf = self.lsdetail.append(parentConfFilesBD,rattr['cn'])
                        else:
                            self.lsdetail.append(parentConfFilesBD,rattr['cn'])
            if not parentPostgreSQLConf is None:
                confrmldap = self.getPostgreSQLConfFromLDAP(pgclustername)
                if not confrmldap is None: 
                    for groupattr in confrmldap.keys():
                        self.lsdetail.append(parentPostgreSQLConf, [self.pgClusterDetailType[groupattr]])
                

    def drawBouncersTree(self):
        self.clearAllForms()
#        self.drawBouncerDetail(None)
        b_frm_ldap = self.getBouncersFromLDAP()
        if not b_frm_ldap is None: 
            for dn, rattr in b_frm_ldap:
                self.lsStartText.append([' '.join(rattr['cn']),dn])


    def drawDatabaseTree(self):
        self.clearAllForms()
        self.clearInstForms()
        

    def drawUsersTree(self):
        self.clearBodyForms()
        m = self.tvdetail.get_model()
        lsiter = []
        if m.iter_has_child(m.get_iter((2,))):
            iter = m.iter_next(m.get_iter((2,0)))
            lsiter = [m.get_value(m.get_iter((2,0)), 0)]
            while iter != None:
                lsiter.append(m.get_value(iter,0))
                iter = m.iter_next(iter)
        nsfrmldap = self.getAllUsersFromLDAP()
        if not nsfrmldap is None:
            for dn, rattr in nsfrmldap:
                if not (' '.join(rattr['cn']) in lsiter) and not (' '.join(rattr['cn']) in self.list_excluded_users):
                    self.lsbody.append([' '.join(rattr['cn']), ''])
        

    def drawNetServicesTree(self):
        self.clearBodyForms()
        m = self.tvdetail.get_model()
        lsiter = []
        if m.iter_has_child(m.get_iter((1,))):
            iter = m.iter_next(m.get_iter((1,0)))
            lsiter = [m.get_value(m.get_iter((1,0)), 0)]
            while iter != None:
                lsiter.append(m.get_value(iter,0))
                iter = m.iter_next(iter)
        nsfrmldap = self.getAllNetServicesFromLDAP()
        if not nsfrmldap is None:
#             print str(nsfrmldap)
            for dn, rattr in nsfrmldap:
#                 print str(rattr)
                if not (' '.join(rattr['cn']) in lsiter) and not (' '.join(rattr['cn']) in self.list_excluded_netservices):
                    self.lsbody.append([' '.join(rattr['cn']), ' '.join(rattr['pgConnectParams'])])

    
    def drawTemplates(self, templatename):
        obj = self.lsdetail.append(None, templatename)
        confrmldap = self.getObjectDetailTreeFromLDAP('cn=' + ''.join(templatename) + ',cn=ConfTemplates,cn=PgConfig,dc=rbc,dc=ru', ['cn'], ldap.SCOPE_ONELEVEL)
        if not confrmldap is None: 
            for dn, rattr in confrmldap:
                self.lsdetail.append(obj, rattr['cn'])
        

    def getObjectDetailTreeFromLDAP(self, cncontext, fltr, scope=ldap.SCOPE_BASE):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s(cncontext, scope,'(cn=*)', fltr)
            
        except Exception, e:
            stdOut.write('Ошибка чтения детализации объекта в LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def getObjectDetailFromLDAP(self, cncontext):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s(cncontext,ldap.SCOPE_BASE,'(cn=*)')
            
        except Exception, e:
            stdOut.write('Ошибка чтения детализации объекта в LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
            
    
    def getBouncerUsersFromLDAP(self, dnpgcluster):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=users,' + dnpgcluster,ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка чтения пользователей LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr


    def getClusterContribsFromLDAP(self, dnpgcluster):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=contribs,' + dnpgcluster,ldap.SCOPE_BASE,'(cn=*)',['pgContribName'])
            
        except Exception, e:
            stdOut.write('Ошибка чтения Contribs LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        
        
    def getClusterSkytoolsFromLDAP(self, dnpgcluster):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=skytools,' + dnpgcluster,ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка чтения Skytools LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        
        
    def getClusterConfFilesFromLDAP(self, dnpgcluster):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=confiles,' + dnpgcluster,ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка чтения Configuration files LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        

    def getPostgreSQLConfFromLDAP(self, dnpgcluster):
        attr = {}
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attrgroups = self.ldap.search_s('cn=postgresql,cn=confiles,' + dnpgcluster,ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            if not attrgroups is None: 
                for dn, grp in attrgroups:
                        attrval = self.ldap.search_s('cn=' + ''.join(grp['cn']) + ',cn=postgresql,cn=confiles,' + dnpgcluster,ldap.SCOPE_ONELEVEL,'(cn=*)')
                        if not attrval is None:
                            for dn, rattr in attrval:
                                if not ''.join(grp['cn']) in attr.keys():
                                    attr[''.join(grp['cn'])] = [(''.join(rattr['cn']), ''.join(rattr['pgConfParamValue']))]
                                else:
                                    attr[''.join(grp['cn'])] += [(''.join(rattr['cn']), ''.join(rattr['pgConfParamValue']))]
        except Exception, e:
            stdOut.write('Ошибка чтения Configuration files LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr

        
    def getAllUsersFromLDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('ou=Users,dc=rbc,dc=ru',ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка чтения Users из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
    

    def getAllNetServicesFromLDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=PgNetServices,cn=PgContext,dc=rbc,dc=ru',ldap.SCOPE_ONELEVEL,'(cn=*)',['cn', 'pgConnectParams'])
            
        except Exception, e:
            stdOut.write('Ошибка чтения NetServices из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        
        
    def getBouncerDatabasesFromLDAP(self, dnpgcluster):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=dblinks,' + dnpgcluster,ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения списка баз данных из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
    
    def getClusterDatabasesFromLDAP(self, dnpgcluster):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=dbs,' + dnpgcluster,ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения списка баз данных из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
    
    def getQueuesDatabaseFromLDAP(self, dnpgcluster, dbname):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=pgqueues, cn=' + dbname + ', cn=dbs,' + dnpgcluster,ldap.SCOPE_SUBTREE,'(&(cn=*)(objectclass=rbcPgSkQueue))',['cn'])
            
        except ldap.LDAPError, e:
            if e.__class__ != ldap.NO_SUCH_OBJECT:
                stdOut.write('Ошибка получения списка очередей базы данных ' + dbname + ' из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
    
    def getHostsFromLDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=PgHosts,cn=PgConfig,dc=rbc,dc=ru',ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения списка хостов из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        
    
    def clearInstForms(self):
        self.cbhost.set_active(-1)
        m = self.cbhost.get_model()
        self.cbhost.set_model(None)
        m.clear()
        self.cbhost.set_model(m)
        self.edport.set_text('')
        self.cbcluster.set_active(-1)
        m = self.cbcluster.get_model()
        self.cbcluster.set_model(None)
        m.clear()
        self.cbcluster.set_model(m)
        self.edpgversion.set_text('')
        self.edpgwalsize.set_text('')
        self.edpgblocksize.set_text('')
        self.edpgwalblocksize.set_text('')
        self.edpgversionupgr.set_text('')
        self.edpgwalsizeupgr.set_text('')
        self.edpgblocksizeupgr.set_text('')
        self.edpgwalblocksizeupgr.set_text('')        
        self.chkinstsoft.set_active(False)
        self.chkpreinstsoft.set_active(False)
        self.chkschemainst.set_active(False)

    
    def clearAllForms(self):
        self.lsStartText.clear()
        self.lsdetail.clear()
        self.lsbody.clear()

        
    def clearBodyForms(self):
        self.lsbody.clear()

        
    def getRealHostname(self, clname):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=' + clname + ',cn=PgHosts,cn=PgConfig,dc=rbc,dc=ru',ldap.SCOPE_BASE,'(cn=*)',['dbaHostName'])
        except Exception, e:
            stdOut.write('Ошибка получения списка кластеров из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        if not attr is None: 
            for dn, rattr in attr:
                return ' '.join(rattr['dbaHostName'])
        else:
            return clname
        
    def getUsersFromLDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('ou=Users,dc=rbc,dc=ru', ldap.SCOPE_ONELEVEL,'(cn=*)', ['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения списка Пользователей из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr        
        
    def getClustersFromLDAP(self, hostname = None):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            if hostname == None:
                attr = self.ldap.search_s('cn=PgClusters,cn=PgContext,dc=rbc,dc=ru',ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            else:
                attr = self.ldap.search_s('cn=PgClusters,cn=PgContext,dc=rbc,dc=ru',ldap.SCOPE_ONELEVEL,'(dbaHostName=' + hostname + ')',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения списка кластеров из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr

    def getBouncersFromLDAP(self):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=PgBouncers,cn=PgContext,dc=rbc,dc=ru', ldap.SCOPE_ONELEVEL,'(cn=*)', ['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения списка PgBouncer-ов из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr

    def getDatabasesFromLDAP(self, clustername):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s('cn=dbs,cn=' + clustername + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru',ldap.SCOPE_ONELEVEL,'(cn=*)',['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения списка кластеров из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr
        

    def getBouncerDetailFromLDAP(self, dnpgcluster):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s(dnpgcluster, ldap.SCOPE_BASE,'(cn=*)')
            
        except Exception, e:
            stdOut.write('Ошибка получения детализации PgBouncer-ов из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr

    def getAnyFromLDAP(self, node):
        attr = None
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attr = self.ldap.search_s(node, ldap.SCOPE_BASE,'(cn=*)', ['cn'])
            
        except Exception, e:
            stdOut.write('Ошибка получения данных из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return attr       
        
        
    def loadPgClassFromLDAP(self, cls, pgclustername):
        if isinstance(cls, pgBouncerAdm) or isinstance(cls, pgClusterAdm) or isinstance(cls, pgDatabaseAdm):
            attrbounc = self.getBouncerDetailFromLDAP(pgclustername)
            if not attrbounc is None:
                for dn, rattr in attrbounc:
                    for attr in rattr:
                        match = re.search(r"^cn\=(\S+),dc=rbc,dc=ru", ' '.join(rattr[attr])) 
                        if match != None:
                            attrset = self.getAnyFromLDAP(' '.join(rattr[attr]))
                            if not attrset is None:
                                for dn, anycn in attrset: 
                                    setattr(cls, attr, anycn["cn"][0])
                        else:
                            setattr(cls, attr, ' '.join(rattr[attr]))
    
    
    def getClusterIPs(self, clustername, clustertype = 'PgBouncers'):
        rtr = ()
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attrset = self.ldap.search_s(clustername, ldap.SCOPE_BASE,'(cn=*)', ['dbaHostName'])
            if attrset != None:
                for dn, attrs in attrset:
                    hostname = self.getRealHostname(''.join(attrs['dbaHostName']))
                    self.sshclient = SSHConnector(hostname)
                    rtr = tuple(self.sshclient.execute("/sbin/ifconfig | grep -A 1 ^eth | grep " + '"inet addr:"' + " | sed -r 's!.*(inet addr:80.68.[0-9]*.[0-9]*).*$!\\1!'|sed 's/inet addr://'").split('\n'))
        except Exception, e:
            stdOut.write('Ошибка получения IP кластера\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return rtr
        
        
    def checkIPsConfDB(self, ips, nshostname, remove = False):
        rtr = []
        diff_rtr = ''
        dn_pghba = ''
        clsfrmldap = self.getObjectDetailTreeFromLDAP('cn=PgClusters,cn=PgContext,dc=rbc,dc=ru',['cn'])
        if not clsfrmldap is None: 
            for r_dn, rattr in clsfrmldap:
                dbahostsfrmldap = self.getObjectDetailFromLDAP('cn=' + ''.join(rattr['cn']) + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
                if not dbahostsfrmldap is None: 
                    for hr_dn, hrattr in dbahostsfrmldap:
                        if ''.join(hrattr['dbaHostName']) == nshostname:
                            cnffrmldap = self.getObjectDetailFromLDAP('cn=pg_hba,cn=confiles,cn=' + ''.join(rattr['cn']) + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru')
                            if not cnffrmldap is None: 
                                dn_pghba = 'cn=pg_hba,cn=confiles,cn=' + ''.join(rattr['cn']) + ',cn=PgClusters,cn=PgContext,dc=rbc,dc=ru'
                                for c_dn, cattr in cnffrmldap:
                                    cnftext = ''.join(cattr['pgbConfigSettings']).split('\n')
                                    for cnfrow in cnftext:
                                        if not ('host\tall\t\tall\t\t' + ips + '/32\tldap\tldapserver="' + ldap_mirrors + '" ldapbinddn="uid=pgusersearch,ou=Users,dc=rbc,dc=ru" ldapbindpasswd="gjbob" ldapbasedn="cn=users,' + hr_dn + '"' in cnfrow):
                                            rtr += [cnfrow]
                                        else:
                                            return None, None
                                    diff_rtr += 'host\tall\t\tall\t\t' + ips + '/32\tldap\tldapserver="' + ldap_mirrors + '" ldapbinddn="uid=pgusersearch,ou=Users,dc=rbc,dc=ru" ldapbindpasswd="gjbob" ldapbasedn="cn=users,' + hr_dn + '"    # Autogenerated ldap PgBouncer'
        if rtr != []:
            if not remove:
                rtr += [diff_rtr]  
            return dn_pghba ,'\n'.join(rtr)
        else:
            return rtr
    
    
    def prepareIPsConfDB(self, newtext):
        self.ldif2LDAP = [((ldap.MOD_REPLACE), 'pgbConfigSettings', newtext)]
            
            
    def updateIPsConfDB(self, basedn):
        if self.ldif2LDAP != {}:
            try:
                login, passw = dlgLoginPasswInput.AuthFromKeyring('pgadmin', 'uid=pgadmin,ou=Users,dc=rbc,dc=ru')
                self.ldap.bind_s(login, passw)
                for rls in self.ldif2LDAP:
                    self.ldap.modify_s(basedn, [rls]) 
            except Exception, e:
                stdOut.write('Ошибка обновления записи в LDAP\n' + str(e) + '\n')
            finally:
                self.ldap.bind_s('','')

            
    def compareConfFileDB(self, nsname, clustername):
        try:
            for ips in self.getClusterIPs(clustername):
                if ips != '':
                    nsobj =  self.getObjectDetailFromLDAP('cn=' + nsname + ',cn=PgNetServices,cn=PgContext,dc=rbc,dc=ru')
                    if not nsobj is None:
                        for dn, rattr in nsobj:
                            dn_pghba, newtext = self.checkIPsConfDB(ips, ''.join(rattr['dbaHostName']))
                            if not newtext is None:
                                self.ldif2LDAP = {}
                                self.prepareIPsConfDB(newtext)
                                self.updateIPsConfDB(dn_pghba)
                                self.doUploadConfFilesBD(dn_pghba.split(',cn=')[2], ('pg_hba',))
        except:
            return 1001
        
            
    def searchMaxCntFromLDAP(self, basedn, flter):
        rtr = 0
        try:
            login, passw = dlgLoginPasswInput.AuthFromKeyring('pgusersearch', 'uid=pgusersearch,ou=Users,dc=rbc,dc=ru')
            self.ldap.bind_s(login, passw)
            attrset = self.ldap.search_s(basedn, ldap.SCOPE_SUBTREE,'(' + flter + '=*)', [flter,])
            if attrset != None:
                for dn, attrs in attrset:
                    for r in attrs:
                        if r > rtr:
                            rtr = r
        except Exception, e:
            stdOut.write('Ошибка получения максимального значения ветки из LDAP\n' + str(e) + '\n')
        finally:
            self.ldap.bind_s('','')
        return rtr
    
                
    def mainmenuSave2LDAP(self, subject):
        self.doUpdate2LDAP()

    def mainmenuDrop2LDAP(self, subject):
        self.LDAPpdated()

    def mainmenuAdmRules(self, subject):
        self.nbmain.set_current_page(0)

    def mainmenuInstallRules(self, subject):
        self.nbmain.set_current_page(1)

    def mainmenuAboutForm(self, subject):
        self.dlgabout.show_all()

    def mainmenuQuit(self, subject):
        self.destroy(subject)
    
    def mainmenuUsersAdm(self, subject):
        dlgAuthUsersAdm()
        
    def mainmenuDrawDatabasesFromClusters(self, subject):
        dlgDrawDatabasesFromClusters(self)
        
    def mainmenuUploadConfFilesBD(self, subject):
        m, path = self.tvdetail.get_selection().get_selected_rows()
        if m.get_value(m.get_iter(path[0][0]), 0) == 'Файлы настроек БД':
            self.doUploadConfFilesBD(self.currentCluster[0], (m.get_value(m.get_iter(path[0]), 0),))
        else:
            self.doUploadConfFilesBD(self.currentCluster[0])
        
    def mainmenuTemplateAdm(self, subject):
        self.MainTemplateAdm()
        
        
    def destroy(self, widget, data=None):
        if not self.SysLogSession is None:
            self.SysLogSession.sshclient.close()
            self.SysLogSession.join(1)
        gtk.main_quit()

    def drawClustersAndDatabases(self):
        rtr = []
        try:
            objs =  self.getClustersFromLDAP()
            if not objs is None:
                for dn, rattr in objs:
                    clobjs = self.getBouncerDetailFromLDAP(dn)
                    if not clobjs is None:
                        for dn, rattr in clobjs:
                            if not 'stdb_' in rattr['cn'][0]:
                                rtr.append('Список баз для кластера ' + rattr['cn'][0] + ' (' + rattr['dbaHostName'][0] + ')')
                                dbs = self.getDatabasesFromLDAP(rattr['cn'][0])
                                if not dbs is None:
                                    for dn, rattr in dbs:
                                        db = self.getBouncerDetailFromLDAP(dn)
                                        if not db is None:
                                            for dn, rattr in db:
                                                if 'description' in rattr.keys():
                                                    rtr.append('    ' + rattr['cn'][0] + ' (' + rattr['description'][0] + ')')
                                                else:
                                                    rtr.append('    ' + rattr['cn'][0])
                                rtr.append('')                   
        finally:
            return rtr

def  main():
    app = App_main()
    gtk.main()



if __name__ == '__main__':
    main()
    
    
