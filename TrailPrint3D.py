"""
TrailPrint3D - Blender插件：将GPS轨迹文件转换为3D打印地形模型

=== 插件功能 ===
本插件可以将GPX或IGC格式的GPS轨迹文件转换成可3D打印的地形模型，
支持添加路径、文字标注、水体、森林等地理要素。

=== 主要特性 ===
1. 支持GPX和IGC文件格式
2. 自动获取真实海拔数据
3. 单色/多色打印模式
4. 可自定义地图大小和形状
5. 支持批量处理多个轨迹文件
6. 内置中文字体支持

=== 数据来源 ===
- 海拔数据: OpenTopoData (SRTM等数据集), Open-Elevation (NASA SRTM)
- 地形数据: Mapzen Terrain Tiles (AWS Public Dataset)
- 地图数据: © OpenStreetMap contributors
- 水体/森林/城市数据: © OpenStreetMap contributors

=== 代码结构概览 ===
1. 导入和全局设置 (第1-150行)
   - 导入必要的Python和Blender模块
   - 定义全局变量和默认值
   
2. 属性定义 (第150-400行)
   - 定义所有UI参数和设置选项
   - 包括地图大小、分辨率、海拔缩放等
   
3. UI操作符 (第400-1100行)
   - 生成、导出、后期处理等操作
   - 缩放、挤出、磁铁孔等工具
   
4. UI面板 (第1100-1500行)
   - 主面板：生成设置
   - 高级面板：详细参数调整
   - 形状面板：文字和底座设置
   
5. 核心工具函数
   - API和缓存管理 (第1500-1900行)
     * 海拔数据API调用
     * 缓存系统提高性能
     
   - 颜色和材质 (第1900-2200行)
     * 预设材质颜色
     * 地形着色系统
     
   - 坐标转换 (第2200-2450行)
     * GPS坐标转Blender坐标
     * 缩放和投影计算
     
   - 海拔数据获取 (第2450-2900行)
     * OpenTopoData API
     * Open-Elevation API
     * Terrain-Tiles API
     
   - 网格处理 (第2900-3100行)
     * 网格细分和优化
     * 异常点修复
     
   - 形状生成 (第3100-3700行)
     * 六边形、八边形底座
     * 文字标注生成
     
   - 单色模式 (第3980-4100行)
     * 路径嵌入地图
     * 适合单色3D打印机
     
   - OpenStreetMap (第4100-4700行)
     * 水体、森林、城市数据
     * 自动着色
     
6. 主生成函数 (第5000-6000行)
   - runGeneration(): 核心生成流程
   - 整合所有功能模块
"""


bl_info = {
    "name": "TrailPrint3D",
    "blender": (4, 5, 2),
    "category": "Object",
    "version": (2, 23),
    "description": "创建GPS轨迹的3D打印地形模型",
    "warning": "",
    "doc_url": "",
    "tracker_url": "",
    "support": "COMMUNITY"
}

# 插件分类标识
# 设置为完整版本，开放所有功能（移除Patreon限制）
category = "TrailPrint3D+"


import bpy # type: ignore
import webbrowser
import xml.etree.ElementTree as ET
import math
import requests # type: ignore
import time
from datetime import date
from datetime import datetime
import bmesh # type: ignore
from mathutils import Vector, bvhtree, Euler
import os
import sys
import json
import platform
import zlib
import struct


gpx_file_path = ""
exportPath = ""
shape = ""
name = ""
size =  48
num_subdivisions = 8
scaleElevation = 5
pathThickness = 1.2
pathScale = 0.8
shapeRotation = 0
overwritePathElevation = False
autoScale = 1
dataset = "srtm30m"  # OpenTopoData dataset

textFont = ""
textSize = 0
overwriteLength = ""
overwriteHeight = ""
overwriteTime = ""
outerBorderSize = 0

minLat = 0
maxLat = 0
minLon = 0
maxLon = 0

lowestZ = 0
highestZ = 0


overwritePathElevation = False
centerx = 0
centery = 0
total_length = 0
total_elevation = 0
total_time = 0
time_str = ""
elevationOffset = 0
# Conversion factor: 1 degree latitude/longitude ≈ 111320 meters
LAT_LON_TO_METERS = 111.32
additionalExtrusion = 0
specialCollection = [("----", "----", "")]
duration = 0
api = 0
fixedElevationScale = False
minThickness = 7
selfHosted = ""
opentopoAdress = ""
GPXsections = 0

scaleHor = 0

MapObject  = None
plateobj = None
textobj = None

# Define a path to store the counter data
counter_file = os.path.join(bpy.utils.user_resource('CONFIG'), "api_request_counter.json")
elevation_cache_file = os.path.join(bpy.utils.user_resource('CONFIG'), "elevation_cache.json")
# Set up a cache directory for Terrarium tiles
terrarium_cache_dir = os.path.join(bpy.utils.user_resource('CONFIG'), "terrarium_cache")
if not os.path.exists(terrarium_cache_dir):
    os.makedirs(terrarium_cache_dir)

# In-memory elevation cache
_elevation_cache = {}
cacheSize = 100000

#PANEL----------------------------------------------------------------------------------------------------------

def shape_callback(self,context):
    if self.shape == "HEXAGON INNER TEXT" or self.shape == "HEXAGON OUTER TEXT" or self.shape =="OCTAGON OUTER TEXT" or self.shape == "HEXAGON FRONT TEXT":
        try:
            bpy.utils.register_class(MY_PT_Shapes)
        except RuntimeError:
            pass
    else:
        try:
            bpy.utils.unregister_class(MY_PT_Shapes)
        except RuntimeError:
            pass

# Cache the collection names
def get_external_collections(path):
    if not os.path.exists(path):
        return []
    with bpy.data.libraries.load(path, link=True) as (data_from, _):
        return list(data_from.collections)

# Update dropdown items dynamically when panel is drawn
def update_collection_items(self, context):

    print("Updating")
    path = bpy.context.scene.tp3d.specialBlend_path
    path = bpy.path.abspath(path)
    names = get_external_collections(path)
    print(names)
    global specialCollection
    specialCollection = [(name, name, "") for name in names]

def dynamic_specialCollection_items(self, context):
    return specialCollection
    
# Define a Property Group to store variables
class MyProperties(bpy.types.PropertyGroup):
    file_path: bpy.props.StringProperty(
        name="文件路径",
        description="选择一个文件",
        default="",
        maxlen=1024,
        subtype='FILE_PATH'  # Enables file selection
    )# type: ignore
    export_path: bpy.props.StringProperty(
        name="导出路径",
        description="保存 STL 文件的位置",
        default="",
        maxlen=1024,
        subtype='DIR_PATH'  # Enables folder selection
    )# type: ignore
    chain_path: bpy.props.StringProperty(
        name="文件夹路径",
        description="选择包含多个 GPX 文件的文件夹",
        default="",
        maxlen=1024,
        subtype='DIR_PATH'  # Enables folder selection
    )# type: ignore
    trailName: bpy.props.StringProperty(name="名称", default="", description="留空则使用文件名") # type: ignore
    
    shape: bpy.props.EnumProperty(
        name = "形状",
        items=[
            ("HEXAGON", "六边形", "六边形地图"),
            ("SQUARE", "正方形", "正方形地图"),
            ("CIRCLE", "圆形", "圆形地图"),
            ("HEXAGON INNER TEXT", "六边形内文字", "带内嵌文字的六边形地图"),
            ("HEXAGON OUTER TEXT", "六边形外文字", "带背板和文字的六边形地图"),
            ("HEXAGON FRONT TEXT", "六边形正面文字", "带背板和正面文字的六边形地图")
        ],
        default = "HEXAGON OUTER TEXT",
        update = shape_callback #calls shape_callback when user selects diffrent shape to register the Shape Panel
    )# type: ignore
    
    api: bpy.props.EnumProperty(
        name = "api",
        items=[
            ("OPENTOPODATA", "Opentopodata", "Slower but more accurate elevation"),
            ("OPEN-ELEVATION","Open-Elevation","Faster but some regions are low quali"),
            ("TERRAIN-TILES", "Terrain-Tiles", "Currently Fastest available set")
        ],
        default = "TERRAIN-TILES"
    )# type: ignore

    dataset: bpy.props.EnumProperty(
        name = "Dataset",
        items=[
            ("srtm30m", "srtm30m", "Latitudes -60 to 60"),
            ("aster30m","aster30m","global"),
            ("ned10m","ned10m","Continental USA, Hawaii, parts of Alaska"),
            ("mapzen","mapzen","global"),
            ("nzdem8m","nzdem8m","New Zealand 8m"),
            ("eudem25m","eudem25m","Europe")
        ],
        default = "aster30m"
    )# type: ignore

    scalemode: bpy.props.EnumProperty(
        name="scalemode",
        items=[
            ('FACTOR', "Map Scale", "Set a scale based on the Map size"),
            ('COORDINATES', "Coordinates", "Calculate the scale by using 2 Coordinates (Lat/lon)"),
            ('SCALE', "Global Scale", "Set a scale based on the Global Scale (Mercator Projection)")
        ],
        default='FACTOR'
    )# type: ignore
    pathScale: bpy.props.FloatProperty(name = "路径缩放", default = 0.8, min = 0.01, max = 200, description = "路径相对于地图大小/全局缩放的比例（取决于缩放模式）")
    scaleLon1: bpy.props.FloatProperty(name = "经度1", default = 0, description = "第一个坐标的经度")
    scaleLat1: bpy.props.FloatProperty(name = "纬度1", default = 0, description = "第一个坐标的纬度")
    scaleLon2: bpy.props.FloatProperty(name = "经度2", default = 0, description = "第二个坐标的经度")
    scaleLat2: bpy.props.FloatProperty(name = "纬度2", default = 0, description = "第二个坐标的纬度")

    selfHosted: bpy.props.StringProperty(name="自托管API地址", default="", description="必须使用与Opentopodata.org相同的API格式 (https://api.opentopodata.org/v1/)")

    objSize: bpy.props.IntProperty(name="地图大小", default = 100, min = 5, max = 10000,description = "地图的尺寸，单位为毫米")
    num_subdivisions: bpy.props.IntProperty(name = "分辨率", default = 8, min = 1, max = 10, description = "(最大推荐值为8) 数值越高地形越详细，但生成速度越慢")
    scaleElevation: bpy.props.FloatProperty(name = "海拔缩放", default = 2, min = 0, max = 10000, description = "海拔的乘数")
    pathThickness: bpy.props.FloatProperty(name = "路径粗细", default = 1.2, min = 0.1, max = 5, description = "路径的粗细，单位为毫米")
    shapeRotation: bpy.props.IntProperty(name = "形状旋转", default = 0, min = -360, max = 360, description = "形状的旋转角度") 
    overwritePathElevation: bpy.props.BoolProperty(name="覆盖路径海拔", default=True, description = "将路径的每个点投射到地形网格上")
    o_verticesPath: bpy.props.StringProperty(name="路径顶点数", default="")
    o_verticesMap: bpy.props.StringProperty(name="地图顶点数", default="")
    o_mapScale: bpy.props.StringProperty(name="地图比例", default = "")
    o_time: bpy.props.StringProperty(name="生成时间",default="")
    o_apiCounter_OpenTopoData: bpy.props.StringProperty(name="OpenTopoData计数", default = "API限制: ---/1000 每天")
    o_apiCounter_OpenElevation: bpy.props.StringProperty(name="OpenElevation计数", default = "API限制: ---/1000 每月")
    o_centerx: bpy.props.FloatProperty(name = "中心点X", default = 0, description = "路径的X轴中心坐标")
    o_centery: bpy.props.FloatProperty(name = "中心点Y", default = 0, description = "路径的Y轴中心坐标")

    magnetHeight: bpy.props.FloatProperty(name = "磁铁高度", default = 2.5, description = "磁铁孔的高度，单位为毫米")
    magnetDiameter: bpy.props.FloatProperty(name = "磁铁直径", default = 6.3, description = "磁铁孔的直径，单位为毫米")

    textFont: bpy.props.StringProperty(
        name="字体文件",
        description="选择字体文件（留空则自动下载中文字体）",
        default="",
        maxlen=1024,
        subtype='FILE_PATH'  # Enables file selection
    )# type: ignore
    textSize: bpy.props.IntProperty(name="文字大小", default = 5, min = 0, max = 1000, description="文字的大小，单位为毫米")
    textSizeTitle: bpy.props.IntProperty(name="标题文字大小", default = 0, min = 0, max = 1000, description = "设为0则使用'文字大小'的值")
    overwriteLength: bpy.props.StringProperty(name="自定义距离文字", default = "", description="覆盖默认的距离显示")
    overwriteHeight: bpy.props.StringProperty(name="自定义海拔文字", default = "", description="覆盖默认的海拔显示")
    overwriteTime: bpy.props.StringProperty(name="自定义时间文字", default = "", description="覆盖默认的时间显示")
    outerBorderSize: bpy.props.IntProperty(name="边框大小(%)", default = 20, min = 0, max = 1000, description="仅用于带底板的形状")
    text_angle_preset: bpy.props.IntProperty(name="文字角度", description="在形状上旋转文字的角度", default=0, min = 0, max = 260)
    plateThickness: bpy.props.FloatProperty(name="底板厚度", default = 5, description="额外底板的厚度")
    plateInsertValue: bpy.props.FloatProperty(name="底板插入深度", default = 2, description="地图在底板中的切口深度，0表示忽略")

    tileSpacing: bpy.props.FloatProperty(name="瓦片间距", default = 0, description="扩展时瓦片之间的距离")



    minThickness: bpy.props.IntProperty(name="最小厚度", default = 7, min = 0, max = 1000, description="在地图最低点增加的厚度，确保打印强度")
    xTerrainOffset: bpy.props.FloatProperty(name="X轴地形偏移", default = 0, description="使地图在X方向上相对于路径产生偏移")
    yTerrainOffset: bpy.props.FloatProperty(name="Y轴地形偏移", default = 0, description="使地图在Y方向上相对于路径产生偏移")

    rescaleMultiplier: bpy.props.FloatProperty(name = "缩放倍数", default = 1, min = 0, max = 10000, description="海拔重新缩放的倍数")
    thickenValue: bpy.props.FloatProperty(name="加厚值", default = 1, description = "使地图增加指定厚度，单位为毫米")
    fixedElevationScale: bpy.props.BoolProperty(name="固定海拔高度", default=False, description = "强制海拔高度为10mm（从最高点到最低点），海拔缩放系数仍然生效")
    singleColorMode: bpy.props.BoolProperty(name="单色模式", default = True, description = "适合单色3D打印机，合并所有部分为单一对象")
    tolerance: bpy.props.FloatProperty(name="路径容差", default = 0.2, description="单色模式下路径与地形的融合容差值")
    disableCache: bpy.props.BoolProperty(name="禁用缓存", default = False, description = "如果网格出现孔洞或异常，禁用缓存可能有帮助")
    ccacheSize: bpy.props.IntProperty(name = "缓存大小", default = 50000, min = 0, description="海拔数据缓存的最大条目数")
    
    # 旗帜标记选项
    addFlags: bpy.props.BoolProperty(name="添加旗帜标记", default = False, description="在最低点和最高点添加起点/终点旗帜，用于标记地形极值点")
    flagHeight: bpy.props.FloatProperty(name="旗帜高度", default = 5.0, min = 1.0, max = 30.0, description="旗杆高度，单位毫米")
    flagWidth: bpy.props.FloatProperty(name="旗面宽度", default = 3.0, min = 0.5, max = 10.0, description="旗面宽度，单位毫米")


    sAdditionalExtrusion: bpy.props.FloatProperty(name="附加拉伸值",default = 0, description="内部使用的拉伸值")
    sAutoScale: bpy.props.FloatProperty(name="自动缩放",default = 1, description="自动计算的缩放系数")
    sScaleHor: bpy.props.FloatProperty(name="水平缩放",default = 1, description = "地图的水平缩放系数")
    sElevationOffset: bpy.props.FloatProperty(name="海拔偏移", default = 0, description="海拔的基准偏移值")
    sMapInKm: bpy.props.FloatProperty(name = "地图长度(公里)", default = 0, description = "地图尺寸对应的实际公里数")

    col_wActive: bpy.props.BoolProperty(name="包含水体", default=False, description = "包含水体（湖泊、池塘）（实验性功能），海洋暂不支持")
    col_wArea: bpy.props.FloatProperty(name="水体大小阈值", default = 1, description = "小于此阈值的湖泊将被忽略")
    col_fActive: bpy.props.BoolProperty(name="包含森林", default=False, description = "包含森林区域（实验性功能）")
    col_fArea: bpy.props.FloatProperty(name="森林大小阈值", default = 10, description = "小于此阈值的森林将被忽略")
    col_cActive: bpy.props.BoolProperty(name="包含城市边界", default=False, description = "包含城市边界（实验性功能）")
    col_cArea: bpy.props.FloatProperty(name="城市大小阈值", default = 1, description = "小于此阈值的城市将被忽略")
    col_KeepManifold: bpy.props.BoolProperty(name="保留非流形对象", default=False, description = "保留破损的/非流形的水体部分")
    col_PaintMap: bpy.props.BoolProperty(name="绘制地图", default=True, description = "在地图上绘制而不是生成单独的对象（推荐MAC用户使用）")

    mountain_treshold:bpy.props.IntProperty(name="山地阈值", default = 60, min = 0, max = 100,subtype='PERCENTAGE', description="高于此百分比高度的区域将着色为山地")
    cl_thickness: bpy.props.FloatProperty(name="等高线粗细", default = 0.2, description = "等高线的粗细，单位为毫米")
    cl_distance: bpy.props.FloatProperty(name="等高线间距", default = 2, description = "等高线之间的距离")
    cl_offset: bpy.props.FloatProperty(name="等高线偏移", default = 0.0, description = "等高线的起始偏移量")

    show_stats: bpy.props.BoolProperty(name="附加信息", default=False)
    show_coloring: bpy.props.BoolProperty(name="包含元素", default=False)
    show_chain: bpy.props.BoolProperty(name="批量生成", default=False)
    show_map: bpy.props.BoolProperty(name="地图设置",default=False)
    show_pin: bpy.props.BoolProperty(name="图钉标记",default=False)
    show_special: bpy.props.BoolProperty(name="特殊功能",default=False)
    show_postProcess: bpy.props.BoolProperty(name="后期处理", default = False)
    show_api: bpy.props.BoolProperty(name="API设置", default=False)
    show_attribution: bpy.props.BoolProperty(name="数据来源", default = False)

    cityname: bpy.props.StringProperty(name="城市名称", default="Berlin", description = "获取城市的坐标")
    pinLat: bpy.props.FloatProperty(name="纬度", default = 48.00, description="图钉标记的纬度")
    pinLon: bpy.props.FloatProperty(name="经度", default = 8.00, description="图钉标记的经度")

    mapmode: bpy.props.EnumProperty(
        name="mapmode",
        items=[
            ('FROMPLANE', "From Plane", "Generate the Map from a Flat Plane"),
            ('FROMCENTER', "From Point", "Generate the Map from a Point coordinate and a Radius"),
            ('2POINTS', "2 Points", "Generate the Map from 2 Coordinates")
        ],
        default='FROMPLANE'
    )# type: ignore

    jMapLat: bpy.props.FloatProperty(name="纬度", default = 49.00)
    jMapLon: bpy.props.FloatProperty(name="经度", default = 9.00)
    jMapRadius: bpy.props.FloatProperty(name="半径(公里)", default = 200)

    jMapLat1: bpy.props.FloatProperty(name="Latitude1", default = 48.00)
    jMapLat2: bpy.props.FloatProperty(name="Latitude2", default = 49.00)
    jMapLon1: bpy.props.FloatProperty(name="Longitude1", default = 8.00)
    jMapLon2: bpy.props.FloatProperty(name="Longitude2", default = 9.00)

    specialBlend_path: bpy.props.StringProperty(
        name="特殊模板路径",
        description="选择特殊模板.blend文件（TP3dSpecial.blend）",
        default="",
        maxlen=1024,
        subtype='FILE_PATH'
    )

    # Custom property to store selection
    specialCollectionName: bpy.props.EnumProperty(
        name="特殊集合",
        description="从外部.blend文件中选择一个集合",
        items=dynamic_specialCollection_items
    )# type: ignore

    

# Define the operator (script execution)
class MY_OT_runGeneration(bpy.types.Operator):
    bl_idname = "wm.run_my_script"
    bl_label = "生成"
    bl_description = "使用当前设置生成路径和地图"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        
        runGeneration(0)

        bpy.ops.ed.undo_push()
        
        return {'FINISHED'}

class MY_OT_ExportSTL(bpy.types.Operator):
    bl_idname = "wm.run_my_script5"
    bl_label = "导出 STL/OBJ"
    bl_description = "将选定对象导出为单独的STL文件（如果对象包含材质则导出为OBJ）"

    def execute(self, context):
        
        global exportPath
        exportPath = bpy.context.scene.tp3d.get('export_path', None)

        if exportPath == None:
            show_message_box("导出路径为空。请为完成的文件选择一个目录")
            return {'FINISHED'}
    
        exportPath = bpy.path.abspath(exportPath)

        if not exportPath or exportPath == "":
            show_message_box("导出路径为空！请选择一个有效的文件夹。")
            return {'FINISHED'}
        if not os.path.isdir(exportPath):
            show_message_box(f"无效的导出目录：{exportPath}。请选择一个有效的目录。")
            return {'FINISHED'}
        
        if not bpy.context.selected_objects:
            show_message_box("请选择要导出的对象")
            return{'FINISHED'}
        
        export_selected_to_STL()

        
        return {'FINISHED'}


def open_website(self, context):
    webbrowser.open("https://github.com/EmGi3D/TrailPrint3D") 

# Operator to open a website
class MY_OT_OpenWebsite(bpy.types.Operator):
    bl_idname = "wm.open_website"
    bl_label = "访问项目主页"
    bl_description = "访问TrailPrint3D项目主页获取更多信息和支持"

    def execute(self, context):
        open_website(self, context)
        return {'FINISHED'}

def open_discord(self, context):
    webbrowser.open("https://discord.gg/C67H9EJFbz") 

# Operator to open a website
class MY_OT_JoinDiscord(bpy.types.Operator):
    bl_idname = "wm.join_discord"
    bl_label = "加入Discord"
    bl_description = "TrailPrint3D的Discord社区！"

    def execute(self, context):
        open_discord(self, context)
        return {'FINISHED'}
    
class MY_OT_Rescale(bpy.types.Operator):
    bl_idname = "wm.rescale"
    bl_label = "缩放Z轴高度"
    bl_description = "重新缩放当前选中对象的海拔高度"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        multiZ = bpy.context.scene.tp3d.get('rescaleMultiplier', 1)

        selected_objects = [obj for obj in bpy.context.selected_objects if obj.type in {'MESH', 'CURVE'}]
        lowestZ = 1000

        print("Rescaling")
        for obj in selected_objects:
            if obj.type == 'MESH':
                mesh = obj.data
                for i, vert in enumerate(mesh.vertices):
                    if vert.co.z < lowestZ and vert.co.z > 0.1:
                        lowestZ = vert.co.z
            if obj.type == "CURVE":
                if lowestZ == 1000:
                    for spline in obj.data.splines:
                        for point in spline.bezier_points:
                            if point.co.z > 0.1 and point.co.z < lowestZ:
                                lowestZ = point.co.z

        print(f"lowestZ: {lowestZ}")

        for obj in selected_objects:      
            print(obj.name)
            if lowestZ != 1000 and obj.type == "MESH":
                    bpy.context.view_layer.objects.active = obj  # Make it active
                    bpy.ops.object.mode_set(mode='EDIT')
                    # Access mesh data
                    mesh = bmesh.from_edit_mesh(obj.data)
                    for v in mesh.verts:
                        if v.co.z > 0.1:
                            v.co.z = (v.co.z - lowestZ) * (multiZ) + lowestZ
                    bmesh.update_edit_mesh(obj.data)    
                    bpy.ops.object.mode_set(mode='OBJECT')  # Exit Edit Mode  
            if lowestZ != 1000 and obj.type =="CURVE":
                # Access curve splines
                for spline in obj.data.splines:
                    for point in spline.bezier_points:
                        if point.co.z > -0.5:
                            point.co.z = (point.co.z - lowestZ) * (multiZ) + lowestZ
                    for point in spline.points:  # For NURBS
                        if point.co.z > -0.5:
                            point.co.z = (point.co.z - lowestZ) * (multiZ) + lowestZ

            bpy.ops.object.mode_set(mode='OBJECT')  # Exit Edit Mode

            if "Elevation Scale" in obj:
                obj["Elevation Scale"] *= multiZ

        print(f"Scaled all elevation points by Factor {multiZ} on {len(selected_objects)} object(s).")

        return {'FINISHED'}

class MY_OT_thicken(bpy.types.Operator):
    bl_idname="wm.thicken"
    bl_label = "加厚地图"
    bl_description = "增加选中地图的厚度"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self,context):
        
        selected_objects = context.selected_objects
        val = bpy.context.scene.tp3d.thickenValue

        bpy.context.tool_settings.mesh_select_mode = (False, False, True)

        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)

        if not selected_objects:
            show_message_box("未选择任何对象。")
            return {'CANCELLED'}

        for zobj in selected_objects:
            # Check if the custom property 'Object type' exists
            if "Object type" in zobj:
                print(zobj.name)
                if zobj["Object type"] == "TRAIL" or zobj["Object type"] == "WATER" or zobj["Object type"] == "FOREST" or zobj["Object type"] == "CITY":
                    zobj.location.z += val
                elif zobj["Object type"] == "MAP" :
                    zobj.select_set(True)
                    bpy.context.view_layer.objects.active = zobj
                    selectBottomFaces(zobj)
                    bpy.ops.mesh.select_more()
                    bpy.ops.mesh.select_all(action='INVERT')
                    mesh = bmesh.from_edit_mesh(zobj.data)
                    
                    verts_to_move = set()
                    for face in mesh.faces:
                        if face.select:
                            verts_to_move.update(face.verts)

                    for vert in verts_to_move:
                        vert.co.z += val
                    bpy.ops.object.mode_set(mode='OBJECT')
                    bpy.ops.object.select_all(action='DESELECT')
                    zobj.select_set(False)
                    zobj["minThickness"] += val
                    
        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)

                    


        return {'FINISHED'}

class MY_OT_PinCoords(bpy.types.Operator):
    bl_idname="wm.pincoords"
    bl_label = "添加坐标图钉"
    bl_description = "在指定坐标处放置一个图钉标记"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        
        minThickness = bpy.context.scene.tp3d.get("minThickness",7)

        centerlat = bpy.context.scene.tp3d.get("pinLat",0)
        centerlon = bpy.context.scene.tp3d.get("pinLon",0)


        xp,yp,zp = convert_to_blender_coordinates(float(centerlat),float(centerlon),0,0)
        name = "Pin_" + str(round(centerlat,2)) + "." + str(round(centerlon,2))

        #Delete existing object with same name (optional)
        if name in bpy.data.objects:
            bpy.data.objects.remove(bpy.data.objects[name], do_unlink=True)

        #Creatin the Cone
        bpy.ops.mesh.primitive_cone_add(
            vertices=16,
            radius1=0.4,
            radius2=0.8,
            depth=4,
            location=(xp, yp, minThickness + 2)  # Position base at Z=0
        )
        pin = bpy.context.active_object
        pin.name = name

        return {'FINISHED'}

class MY_OT_MagnetHoles(bpy.types.Operator):
    bl_idname = "wm.magnetholes"
    bl_label = "磁铁孔"
    bl_options = {'REGISTER', 'UNDO'}


    
    def execute(self,context):

        selected_objects = context.selected_objects

        if not selected_objects:
            show_message_box("未选择任何对象")
            return('CANCELLED')
        
        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)

        for zobj in selected_objects:

            if zobj.type != 'MESH':
                continue

            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj

            obj_size = bpy.context.scene.tp3d.objSize

            #Check for selection and custom property
            if zobj:
                if "objSize" in zobj.keys():
                    obj_size = zobj["objSize"]
            elif not zobj:
                    print("Select a Map.")
                    return

            magnetDiameter = bpy.context.scene.tp3d.magnetDiameter
            magnetHeight = bpy.context.scene.tp3d.magnetHeight

            #Flip normals and Get bottom faces
            selectBottomFaces(zobj)

            #get the lowest zValue of one the faces
            zValue = 0

            # Switch to Edit Mode
            bpy.ops.object.mode_set(mode='EDIT')
            mesh = bmesh.from_edit_mesh(zobj.data)

            # Get the world matrix to convert local to global coordinates
            world_matrix = zobj.matrix_world

            # Collect global Z-values of selected faces
            z_values = [
                (world_matrix @ face.calc_center_median()).z
                for face in mesh.faces if face.select
            ]
            
            zValue = min(z_values)

            bpy.ops.object.mode_set(mode='OBJECT')


            #Set 3D cursor to object's origin
            bpy.context.scene.cursor.location = zobj.location

            #Create 4 cylinders around the object
            radius = obj_size / 3
            angle_step = math.radians(90)
            created_cylinders = []

            for i in range(4):
                angle = i * angle_step
                offset_x = math.cos(angle) * radius
                offset_y = math.sin(angle) * radius
                pos = zobj.location + Vector((offset_x, offset_y, zValue))

                bpy.ops.mesh.primitive_cylinder_add(
                    radius=magnetDiameter / 2,
                    depth=magnetHeight,
                    location=pos
                )
                cyl = bpy.context.active_object
                created_cylinders.append(cyl)

            #Merge cylinders into one object
            bpy.ops.object.select_all(action='DESELECT')
            for cyl in created_cylinders:
                cyl.select_set(True)
            bpy.context.view_layer.objects.active = created_cylinders[0]
            bpy.ops.object.join()
            merged_cylinders = bpy.context.active_object

            #Perform boolean difference
            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj

            bool_mod = zobj.modifiers.new(name="MagnetCutout", type='BOOLEAN')
            bool_mod.operation = 'DIFFERENCE'
            bool_mod.object = merged_cylinders

            bpy.ops.object.modifier_apply(modifier=bool_mod.name)

            #Cleanup - delete the merged cutter object
            bpy.data.objects.remove(merged_cylinders, do_unlink=True)

            zobj["MagnetHoles"] = True

            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(False)

        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)
        

        print("Magnet holes Added")


        return{'FINISHED'}

class MY_OT_Dovetail(bpy.types.Operator):
    bl_idname = "wm.dovetail"
    bl_label = "燕尾槽"
    bl_options = {'REGISTER', 'UNDO'}
    
    def execute(self,context):

        selected_objects = context.selected_objects

        if not selected_objects:
            show_message_box("未选择任何对象")
            return('CANCELLED')
        
        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)
        
        for zobj in selected_objects:

            if zobj.type != 'MESH':
                continue

            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj


            #Check for selection and custom property
            if zobj:
                if "objSize" not in zobj.keys():
                    break
            
            obj_size = zobj["objSize"]
            dovetailSize = 15
            dovetailHeight = 3


            if obj_size <= 50:
                dovetailSize = 5
            elif obj_size <= 75:
                dovetailSize = 10

            #Flip normals and Get bottom faces
            selectBottomFaces(zobj)

            #get the lowest zValue of one the faces
            zValue = 0

            # Switch to Edit Mode
            #bpy.ops.object.mode_set(mode='EDIT')
            mesh = bmesh.from_edit_mesh(zobj.data)

            # Get the world matrix to convert local to global coordinates
            world_matrix = zobj.matrix_world

            # Collect global Z-values of selected faces
            z_values = [
                (world_matrix @ face.calc_center_median()).z
                for face in mesh.faces if face.select
            ]
            
            zValue = min(z_values)

            bpy.ops.object.mode_set(mode='OBJECT')


            #Set 3D cursor to object's origin
            bpy.context.scene.cursor.location = zobj.location

            #Create 4 cylinders around the object
            radius = obj_size/2 * 0.866 - dovetailSize/2
            angle_step = math.radians(60)
            steps = 6
            created_cylinders = []

            for i in range(steps):
                angle = i * angle_step + math.radians(30)
                offset_x = math.cos(angle) * radius
                offset_y = math.sin(angle) * radius
                pos = zobj.location + Vector((offset_x, offset_y, zValue + dovetailHeight/2))
                rotation = Euler((0, 0, angle - math.radians(90)), 'XYZ')

                bpy.ops.mesh.primitive_cylinder_add(
                    vertices = 3,
                    radius=dovetailSize,
                    depth=dovetailHeight,
                    location=pos,
                    rotation = rotation
                )
                cyl = bpy.context.active_object
                created_cylinders.append(cyl)
        
            #Merge cylinders into one object
            bpy.ops.object.select_all(action='DESELECT')
            for cyl in created_cylinders:
                cyl.select_set(True)
            bpy.context.view_layer.objects.active = created_cylinders[0]
            bpy.ops.object.join()
            merged_cylinders = bpy.context.active_object

            #Select top faces of the Triangles to scale them up slightly
            selectTopFaces(merged_cylinders)

            mesh = bmesh.from_edit_mesh(merged_cylinders.data)
            # Scale factor
            scale_factor = 1.05

            # Scale each selected face from its own center
            for face in mesh.faces:
                if face.select:
                    center = face.calc_center_median()
                    for vert in face.verts:
                        direction = vert.co - center
                        vert.co = center + direction * scale_factor

            # Update the mesh
            bmesh.update_edit_mesh(merged_cylinders.data, loop_triangles=False)

            bpy.ops.object.mode_set(mode='OBJECT')

            #Perform boolean difference
            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(True)
            bpy.context.view_layer.objects.active = zobj

            bool_mod = zobj.modifiers.new(name="DovetailCutout", type='BOOLEAN')
            bool_mod.operation = 'DIFFERENCE'
            bool_mod.object = merged_cylinders
            

            zobj["Dovetail"] = True

            bpy.ops.object.modifier_apply(modifier=bool_mod.name)

            #Cleanup - delete the merged cutter object
            bpy.data.objects.remove(merged_cylinders, do_unlink=True)

            bpy.ops.object.select_all(action='DESELECT')
            zobj.select_set(False)
        
        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)


        print("Dovetail Added")


        return{"FINISHED"}

class MY_OT_TerrainDummy(bpy.types.Operator):
    bl_idname = "wm.dummy"
    bl_label = "占位操作符"
    bl_description = "此功能现已完全开放"
    def execute(self,context):
        show_message_box("所有功能现已完全开放，无需付费！")
        return{"FINISHED"}
    


class MY_OT_BottomMark(bpy.types.Operator):
    bl_idname = "wm.bottommark"
    bl_label = "底部标记"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self,context):

        selected_objects = context.selected_objects

        if not selected_objects:
            show_message_box("未选择任何对象")
            return('CANCELLED')
        
        bpy.ops.object.select_all(action='DESELECT')
        for zobj in selected_objects:
            zobj.select_set(False)

        generated = False
        for zobj in selected_objects:

            if zobj.type == "MESH" and "objSize" in zobj:

                zobj.select_set(True)
                bpy.context.view_layer.objects.active = zobj

                BottomText(zobj)
                generated = True

                bpy.ops.object.select_all(action='DESELECT')
                zobj.select_set(False)
        
        if generated == False:
            show_message_box("选择中未找到地图对象")

        bpy.context.view_layer.objects.active = selected_objects[0]
        for zobj in selected_objects:
            zobj.select_set(True)



        return{'FINISHED'}
    





    

    

class MY_OT_ColorMountain(bpy.types.Operator):
    bl_idname="wm.colormountain"
    bl_label = "为山地着色"
    bl_description = "为超过指定阈值高度的山地区域添加颜色"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self,context):

        
        selected_objects = bpy.context.selected_objects
        min_treshold = bpy.context.scene.tp3d.mountain_treshold

        #Collect min/max from custom properties
        min_z = None
        max_z = None
        minThickness = None

        if not selected_objects:
            show_message_box("No Object Selected. Please select a Map first")
            return {'CANCELLED'}

        for obj in selected_objects:
            if "lowestZ" in obj.keys() and "highestZ" in obj.keys() and obj["highestZ"] != 0:
                low = obj["lowestZ"]
                high = obj["highestZ"]
                minThickness = obj["minThickness"]
                min_z = low if min_z is None else min(min_z, low)
                max_z = high if max_z is None else max(max_z, high)

        print(f"Lowest Z across objects: {min_z}, Highest Z: {max_z}")

        #Create or get green material
        matG = bpy.data.materials.get("BASE")
       
        #Create or get a gray material
        mat = bpy.data.materials.get("MOUNTAIN")

        #Iterate objects and faces
        for obj in selected_objects:
            if obj.type != 'MESH' or obj["Object type"] != "MAP" or max_z == 0:
                print("Not Applied")
                continue
            print("Apply Mountain Color")


            #obj.data.materials.clear()
            #obj.data.materials.append(matG)  # creates first slot and assigns

            bpy.context.view_layer.objects.active = obj
            bpy.ops.object.mode_set(mode='EDIT')
            bm = bmesh.from_edit_mesh(obj.data)

            #Ensure material exists on the object
            matG_index = obj.data.materials.find("BASE")
            mat_index = obj.data.materials.find("MOUNTAIN")
            if mat_index == -1:  # Material not assigned yet
                obj.data.materials.append(mat)
                mat_index = len(obj.data.materials) - 1
            
            tres = (max_z-min_z)/100 * min_treshold + minThickness
            for face in bm.faces:
                #Skip vertical faces (normal is not pointing up/down)
                if abs(face.normal.z) < 0.02:  
                    continue

                avg_z = sum(v.co.z for v in face.verts) / len(face.verts)
                if avg_z > tres and face.material_index == matG_index:
                    face.material_index = mat_index
                elif avg_z < tres and face.material_index == mat_index:
                    face.material_index = matG_index

            bmesh.update_edit_mesh(obj.data)
            bpy.ops.object.mode_set(mode='OBJECT')



        return {'FINISHED'}

class MY_OT_ContourLines(bpy.types.Operator):
    bl_idname="wm.contourlines"
    bl_label = "等高线"
    bl_description = "在地图上生成等高线"

    def execute(self,context):

        
        selected_objects = bpy.context.selected_objects
        cl_thickness = bpy.context.scene.tp3d.cl_thickness
        cl_distance = bpy.context.scene.tp3d.cl_distance
        cl_offset = bpy.context.scene.tp3d.cl_offset

        size = bpy.context.scene.tp3d.objSize



        if not selected_objects:
            show_message_box("未选择对象。请先选择一个地图对象")
            return {'CANCELLED'}

        for obj in selected_objects:

            if not "Object type" in obj:
                continue
            if obj["Object type"] != "MAP":
                continue

            objs = list(bpy.context.scene.objects)
            for o in objs:
                if "Object type" in o and "PARENT" in o:
                    if o["PARENT"] == obj and  o["Object type"] == "LINES":
                        bpy.data.objects.remove(o, do_unlink=True)
            
            # Deselect everything
            bpy.ops.object.select_all(action='DESELECT')
            
            # Create plane at 3D cursor
            bpy.ops.mesh.primitive_plane_add(size=size + 10, enter_editmode=False, align='WORLD',
                                            location=bpy.context.scene.cursor.location)
            plane = bpy.context.active_object
            plane.name = "CuttingPlane"
            plane.location.z += cl_offset
            
            # Add Array modifier in Z direction
            array_mod = plane.modifiers.new(name="ArrayZ", type='ARRAY')
            array_mod.relative_offset_displace = (0, 0, 0)   # disable relative offset
            array_mod.constant_offset_displace = (0, 0, cl_distance)   # fixed step in Z
            array_mod.use_relative_offset = False
            array_mod.use_constant_offset = True
            array_mod.count = 100  # you can adjust how many slices
            
            # Add Solidify modifier for thickness
            solidify_mod = plane.modifiers.new(name="Solidify", type='SOLIDIFY')
            solidify_mod.thickness = cl_thickness
            
            # Apply modifiers up to solidify
            bpy.context.view_layer.objects.active = plane
            bpy.ops.object.modifier_apply(modifier=array_mod.name)
            bpy.ops.object.modifier_apply(modifier=solidify_mod.name)
            
            # Add Boolean modifier with INTERSECT mode
            bool_mod = plane.modifiers.new(name="Boolean", type='BOOLEAN')
            bool_mod.operation = 'INTERSECT'
            bool_mod.solver = 'MANIFOLD'  # or 'EXACT'
            bool_mod.use_self = False
            bool_mod.use_hole_tolerant = True  # helps with manifold issues
            bool_mod.object = obj

            plane.name = obj.name + "_LINES"

            mat = bpy.data.materials.get("WHITE")
            plane.data.materials.clear()
            plane.data.materials.append(mat)

            writeMetadata(plane,"LINES")
            plane["PARENT"] = obj

            
            # Apply Boolean
            bpy.context.view_layer.objects.active = plane
            
            bpy.ops.object.modifier_apply(modifier=bool_mod.name)



        bpy.ops.object.select_all(action='DESELECT')
        for obj in selected_objects:
            obj.select_set(True)
        bpy.context.view_layer.objects.active = selected_objects[0]
            

        return {'FINISHED'}
    
    
    
# Create the UI Panel
class MY_PT_Generate(bpy.types.Panel):
    bl_label = "创建"
    bl_idname = "PT_EmGi_3DPath+"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "TrailPrint3D"
    

    def draw(self, context):
        layout = self.layout
        props = context.scene.tp3d  # Get properties

        # Add input fields
        layout.separator()  # Adds a horizontal line
        # Add the script execution button
        layout.label(text = "创建文件")
        layout.operator("wm.run_my_script")
        box = layout.box()
        box.prop(props, "file_path")
        box.prop(props, "export_path")
        box.prop(props, "trailName")
        box.prop(props, "shape")
        box.separator()  # Adds a horizontal line
        box.prop(props, "objSize")
        box.prop(props, "num_subdivisions")
        box.prop(props, "scaleElevation")
        box.prop(props, "pathThickness")
        box.prop(props, "scalemode")
        if props.scalemode == "FACTOR":
            box.prop(props, "pathScale")
        elif props.scalemode == "COORDINATES":
            row = box.row()
            row.prop(props,"scaleLat1")
            row.prop(props,"scaleLon1")
            row = box.row()
            row.prop(props,"scaleLat2")
            row.prop(props,"scaleLon2")
        elif props.scalemode == "SCALE":
            box.prop(props, "pathScale")
        else:
            box.label(text=props.scalemode)

        box.prop(props, "overwritePathElevation")

        layout.label(text = props.o_time)
        layout.label(text = "------------------------------")
        

class MY_PT_Advanced(bpy.types.Panel):
    bl_label = "高级选项"
    bl_idname = "PT_Advanced"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "TrailPrint3D"
    
    def draw(self, context):
        layout = self.layout
        props = context.scene.tp3d  # Get properties
        
        #Add input fields

        #STL EXPORT
        box = layout.box()
        box.label(text = "手动导出选定对象为 STL/OBJ")
        box.operator("wm.run_my_script5")

        #MAP
        layout.prop(props,"show_map", icon="TRIA_DOWN" if props.show_map else "TRIA_RIGHT", emboss=True, text="地图设置")
        if props.show_map:
            box = layout.box()
            box.prop(props, "fixedElevationScale")
            box.prop(props, "minThickness")
            box.prop(props, "shapeRotation")
            box.prop(props, "xTerrainOffset")
            box.prop(props, "yTerrainOffset")
            box.prop(props, "singleColorMode")
            box.prop(props, "tolerance")
            box.prop(props, "disableCache")
            box.prop(props, "ccacheSize")
            box.separator()  # Adds a horizontal line
            
            # 旗帜标记选项
            box.prop(props, "addFlags")
            if props.addFlags:
                box.prop(props, "flagHeight")
                box.prop(props, "flagWidth")
            
            box.separator()  # Adds a horizontal line

            box.label(text="自定义地图")
            # 检查是否已生成地图（完全开放）
            if bpy.context.scene.tp3d.sScaleHor != None:
                box.prop(props, "mapmode")
                if props.mapmode == "FROMPLANE":
                    box.operator("wm.terrain", text = "从选定对象创建地图")
                    #Create Blank
                    box.operator("wm.create_blank", text = "创建空白地图")
                    box.operator("wm.extend_tile", text = "扩展选定瓦片")
                    box.prop(props,"tileSpacing")
                elif props.mapmode == "FROMCENTER":
                    row = box.row()
                    row.prop(props, "jMapLat")
                    row.prop(props, "jMapLon")
                    box.prop(props, "jMapRadius")
                    box.operator("wm.fromcentergeneration", text = "从1个点+半径创建地图")
                    box.operator("wm.fromcentergenerationwithtrail", text = "从1个点+半径创建带路径的地图")

                elif props.mapmode == "2POINTS":
                    row = box.row()
                    row.prop(props, "jMapLat1")
                    row.prop(props, "jMapLon1")
                    row = box.row()
                    row.prop(props, "jMapLat2")
                    row.prop(props, "jMapLon2")
                    box.operator("wm.2pointgeneration", text = "从2个点创建地图")
                else:
                    box.label(text=props.scalemode)
                
                box.separator()
                #Merge with Map
                box.operator("wm.mergewithmap",text ="合并到地图")
            
                box.separator()  # Adds a horizontal line
            else:
                box.label(text = "仅在生成地图后可用")
                box.label(text = "(同一会话)")
                box.operator("wm.terrain", text = "从选定对象创建地图")
                box.operator("wm.create_blank", text = "创建空白地图")
                

            layout.separator()  # Adds a horizontal line

        #MULTI - 批量生成功能（完全开放）
        layout.prop(props,"show_chain", icon="TRIA_DOWN" if props.show_chain else "TRIA_RIGHT", emboss=True, text="批量生成")
        if props.show_chain:
            box = layout.box()
            box.label(text = "批量生成")
            box.label(text = "从文件夹中的多个GPX文件创建单个地图")
            box.prop(props, "chain_path")
            box.operator("wm.run_my_script2")
            layout.separator()  # Adds a horizontal line
            

        #INCLUDE ELEMENTS
        layout.prop(props,"show_coloring", icon="TRIA_DOWN" if props.show_coloring else "TRIA_RIGHT", emboss=True, text="包含元素")
        if props.show_coloring:
            boxer = layout.box()
            box = boxer.box()
            box.label(text = "水体")
            box.prop(props, "col_wActive")
            box.prop(props, "col_wArea")
            box = boxer.box()
            box.label(text = "森林")
            box.prop(props, "col_fActive")
            box.prop(props, "col_fArea")
            box = boxer.box()
            box.label(text = "城市边界")
            box.prop(props, "col_cActive")
            box.prop(props, "col_cArea")
            #layout.prop(props, "col_KeepManifold")
            boxer.prop(props,"col_PaintMap")
        
        #PIN
        layout.prop(props,"show_pin", icon="TRIA_DOWN" if props.show_pin else "TRIA_RIGHT", emboss=True, text="图钉标记")
        if props.show_pin:
            box = layout.box()
            box.label(text="通过坐标设置图钉")
            row = box.row()
            row.prop(props, "pinLat")
            row.prop(props, "pinLon")
            box.operator("wm.pincoords", text = "在坐标处添加图钉")
            box.separator()  # Adds a horizontal line
            box.label(text="通过城市名称设置图钉")
            box.prop(props, "cityname")
            box.operator("wm.citycoords",text = "在城市处添加图钉")
        
        #SPECIAL - 特殊功能（完全开放）
        layout.prop(props,"show_special",icon="TRIA_DOWN" if props.show_special else "TRIA_RIGHT", emboss = True, text="特殊功能")
        if props.show_special:
            box = layout.box()
            box.label(text = "使用特殊的手工制作模板")
            box.label(text = "例如：拼图、滑动拼图等")
            box.separator()
            box.prop(props, "specialBlend_path")
            box.operator("wm.update_special_collection", text = "加载 .blend 文件")
            box.prop(props, "specialCollectionName", text="集合")
            box.operator("wm.appendcollection", text = "导入")
        
        #POST PROCESS
        layout.prop(props,"show_postProcess", icon = "TRIA_DOWN" if props.show_postProcess else "TRIA_RIGHT", emboss = True, text="后期处理")
        if props.show_postProcess:
            box = layout.box()
            box.label(text = "执行这些操作后需手动导出对象")
            box.separator()
            box.label(text="山地着色")
            box.prop(props,"mountain_treshold")
            box.operator("wm.colormountain", text = "为山地着色")
            box.separator()

            box.prop(props,"cl_thickness")
            box.prop(props,"cl_distance")
            box.prop(props,"cl_offset")
            box.operator("wm.contourlines")

            box.separator()

            box.label(text="重新缩放选中对象的海拔高度")
            row = box.row()
            row.prop(props, "rescaleMultiplier")
            row.operator("wm.rescale",text = "缩放海拔高度" )
            box.separator()  # Adds a horizontal line

            box.label(text = "将选中对象的地形挤出指定高度")
            box.prop(props,"thickenValue")
            box.operator("wm.thicken", text = "挤出地形")
            box.separator()

            row = box.row()
            row.prop(props,"magnetHeight")
            row.prop(props,"magnetDiameter")
            box.operator("wm.magnetholes", text = "添加磁铁孔")

            box.separator()
            box.operator("wm.dovetail", text = "添加燕尾槽切口")

            box.separator()
            box.operator("wm.bottommark", text = "添加底部标记")


        #API
        layout.prop(props,"show_api", icon="TRIA_DOWN" if props.show_api else "TRIA_RIGHT", emboss=True, text="海拔数据API")
        if props.show_api:
            box = layout.box()
            box.prop(props,"api")
            if props.api == "OPENTOPODATA":
                box.prop(props, "dataset")
                box.separator()  # Adds a horizontal line
                box.label(text="如果您自托管了Opentopodata服务器:")
                box.prop(props, "selfHosted")
                layout.separator()  # Adds a horizontal line

        #STATS
        layout.prop(props,"show_stats", icon="TRIA_DOWN" if props.show_stats else "TRIA_RIGHT", emboss=True, text="统计信息")
        if props.show_stats:
            box = layout.box()
            box.label(text="获取选中地图的生成参数")
            box.operator("object.show_custom_props_popup")
            box = layout.box()
            box.label(text = props.o_verticesPath)
            box.label(text = props.o_verticesMap)
            box.label(text = props.o_mapScale)
            box.label(text = f"水平缩放: {props.sScaleHor}")
            box.label(text = f"地图尺寸: {props.sMapInKm}")
            box.label(text = props.o_time)
            box.separator()  # Adds a horizontal line
            box.label(text = "Opentopodata API调用:")
            box.label(text = props.o_apiCounter_OpenTopoData)
            box.label(text = "OpenElevation API调用:")
            box.label(text = props.o_apiCounter_OpenElevation)
            layout.separator()  # Adds a horizontal line

        #ATTRIBUTION
        layout.prop(props,"show_attribution", icon="TRIA_DOWN" if props.show_attribution else "TRIA_RIGHT", emboss=True, text="数据来源声明")
        if props.show_attribution:
            box = layout.box()
            box.label(text = "数据来源声明")
            box.label(text = "海拔数据来自OpenTopoData，使用SRTM和其他数据集。")
            box.label(text = "海拔数据来自Open-Elevation，基于NASA的航天飞机雷达地形测绘(SRTM)数据。")
            box.label(text = "水体、森林、城市数据 © OpenStreetMap贡献者")
            box.label(text = "地形数据来自Mapzen，基于OpenStreetMap贡献者、NASA SRTM和USGS数据。")
            layout.separator()  # Adds a horizontal line

class MY_PT_Shapes(bpy.types.Panel):
    bl_label = "附加形状设置"
    bl_idname = "PT_ShapeSettings"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "TrailPrint3D"
    
    def draw(self, context):
        layout = self.layout
        props = context.scene.tp3d  # Get properties
        
        #print(f"shape: {props.shape}")
        if props.shape == "HEXAGON INNER TEXT" or props.shape == "HEXAGON OUTER TEXT" or props.shape == "OCTAGON OUTER TEXT" or props.shape == "HEXAGON FRONT TEXT":

            #Add input fields
            layout.prop(props, "textFont")
            layout.prop(props, "textSize")
            layout.prop(props, "textSizeTitle")
            layout.separator()  # Adds a horizontal line
            layout.label(text = "自定义文本内容:")
            layout.prop(props, "overwriteLength")
            layout.prop(props, "overwriteHeight")
            layout.prop(props, "overwriteTime")
            layout.prop(props, "plateThickness")
            layout.prop(props, "outerBorderSize")
            layout.prop(props, "plateInsertValue")
            layout.prop(props, "text_angle_preset")


class OBJECT_OT_ShowCustomPropsPopup(bpy.types.Operator):
    bl_idname = "object.show_custom_props_popup"
    bl_label = "生成参数"
    bl_description = "显示生成此对象时使用的设置参数(需选中地图对象)"
    bl_options = {'REGISTER'}

    MAX_PER_COLUMN = 25
    NORMAL_WIDTH = 400
    DOUBLE_WIDTH = 800

    def draw(self, context):
        layout = self.layout
        obj = context.active_object

        if not obj:
            layout.label(text="未选择活动对象。", icon="ERROR")
            return

        custom_props = [k for k in obj.keys() if not k.startswith("_")]

        if not custom_props:
            layout.label(text="未找到自定义属性。请选择一个地图对象", icon="INFO")
            return

        total = len(custom_props)

        if total > self.MAX_PER_COLUMN:
            split = layout.split(factor=0.5)
            col1 = split.column(align=True)
            col2 = split.column(align=True)

            mid = (total + 1) // 2

            for col, chunk in zip((col1, col2), (custom_props[:mid], custom_props[mid:])):
                for key in chunk:
                    row = col.row()
                    row.label(text=key + ":", icon='DOT')
                    row.label(text=str(obj[key]))
        else:
            col = layout.column(align=True)
            for key in custom_props:
                row = col.row()
                row.label(text=key + ":", icon='DOT')
                row.label(text=str(obj[key]))

    def execute(self, context):
        return {'FINISHED'}

    def invoke(self, context, event):
        obj = context.active_object
        custom_props = [k for k in obj.keys() if not k.startswith("_")] if obj else []
        width = self.DOUBLE_WIDTH if len(custom_props) > self.MAX_PER_COLUMN else self.NORMAL_WIDTH
        return context.window_manager.invoke_props_dialog(self, width=width)

# Register the classes and properties
def register():
    bpy.utils.register_class(MyProperties)
    bpy.types.Scene.tp3d = bpy.props.PointerProperty(type=MyProperties)

    bpy.utils.register_class(MY_OT_runGeneration)
    bpy.utils.register_class(MY_OT_ExportSTL)
    bpy.utils.register_class(MY_PT_Generate)
    bpy.utils.register_class(MY_PT_Advanced)
    bpy.utils.register_class(MY_OT_OpenWebsite)
    bpy.utils.register_class(MY_OT_JoinDiscord)
    bpy.utils.register_class(MY_OT_Rescale)
    bpy.utils.register_class(OBJECT_OT_ShowCustomPropsPopup)
    bpy.utils.register_class(MY_OT_PinCoords)
    bpy.utils.register_class(MY_OT_TerrainDummy)
    bpy.utils.register_class(MY_OT_MagnetHoles)
    bpy.utils.register_class(MY_OT_Dovetail)
    bpy.utils.register_class(MY_OT_thicken)
    bpy.utils.register_class(MY_OT_BottomMark)
    bpy.utils.register_class(MY_OT_ColorMountain)
    bpy.utils.register_class(MY_OT_ContourLines)

    


def unregister():
    del bpy.types.Scene.tp3d
    bpy.utils.unregister_class(MyProperties)

    bpy.utils.unregister_class(MY_OT_runGeneration)
    bpy.utils.unregister_class(MY_OT_ExportSTL)
    bpy.utils.unregister_class(MY_PT_Generate)
    bpy.utils.unregister_class(MY_PT_Advanced)
    bpy.utils.unregister_class(MY_OT_OpenWebsite)
    bpy.utils.unregister_class(MY_OT_JoinDiscord)
    bpy.utils.unregister_class(MY_OT_Rescale)
    bpy.utils.unregister_class(OBJECT_OT_ShowCustomPropsPopup)
    bpy.utils.unregister_class(MY_OT_PinCoords)
    bpy.utils.unregister_class(MY_OT_TerrainDummy)
    bpy.utils.unregister_class(MY_OT_MagnetHoles)
    bpy.utils.unregister_class(MY_OT_Dovetail)
    bpy.utils.unregister_class(MY_OT_thicken)
    bpy.utils.unregister_class(MY_OT_BottomMark)
    bpy.utils.unregister_class(MY_OT_ColorMountain)
    bpy.utils.unregister_class(MY_OT_ContourLines)





#--------------------------------------------------
#Debug
#--------------------------------------------------

def get_chinese_font():
    """
    查找并返回系统中可用的中文字体
    
    功能说明：
    1. 根据操作系统类型查找常见的中文字体
    2. 按优先级依次尝试多个字体文件
    3. 找到第一个可用的字体后立即返回
    
    支持的操作系统：
    - macOS: 苹方、华文黑体、宋体等
    - Windows: 微软雅黑、黑体、宋体等
    - Linux: Noto Sans CJK、文泉驿等
    
    返回值：
        str: 字体文件的完整路径，如果未找到则返回空字符串
    """
    
    # 根据操作系统定义中文字体列表
    if platform.system() == "Darwin":  # macOS系统
        possible_fonts = [
            "/System/Library/Fonts/PingFang.ttc",           # 苹方（推荐）
            "/System/Library/Fonts/STHeiti Light.ttc",      # 华文黑体
            "/System/Library/Fonts/Supplemental/Songti.ttc", # 宋体
            "/Library/Fonts/Arial Unicode.ttf"              # Arial Unicode（备用）
        ]
    elif platform.system() == "Windows":  # Windows系统
        possible_fonts = [
            "C:/Windows/Fonts/msyh.ttc",     # 微软雅黑（推荐）
            "C:/Windows/Fonts/simhei.ttf",   # 黑体
            "C:/Windows/Fonts/simsun.ttc",   # 宋体
            "C:/Windows/Fonts/simkai.ttf"    # 楷体（备用）
        ]
    else:  # Linux系统
        possible_fonts = [
            "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",  # Noto思源
            "/usr/share/fonts/truetype/wqy/wqy-microhei.ttc",          # 文泉驿微米黑
            "/usr/share/fonts/truetype/wqy/wqy-zenhei.ttc",            # 文泉驿正黑
            "/usr/share/fonts/truetype/droid/DroidSansFallbackFull.ttf" # Droid备用
        ]
    
    # 遍历字体列表，找到第一个存在的字体文件
    for font_path in possible_fonts:
        if os.path.exists(font_path):
            print(f"找到可用的中文字体: {font_path}")
            return font_path
    
    # 如果没有找到任何中文字体，打印警告信息
    print("警告: 未找到系统中文字体，文本可能无法正确显示中文")
    return ""

def load_counter():
    if os.path.exists(counter_file):
        try:
            with open(counter_file, "r") as f:
                data = json.load(f)
                return data.get("count_openTopodata", 0), data.get("date_openTopoData", ""), data.get("count_openElevation",0), data.get("date_openElevation","")
        except:
            return 0, "", 0, ""
    return 0, "", 0, ""

# Function to save the counter data
def save_counter(count_openTopodata, date_openTopoData, count_openElevation, date_openElevation):
    with open(counter_file, "w") as f:
        json.dump({"count_openTopodata": count_openTopodata, "date_openTopoData": date_openTopoData, "count_openElevation": count_openElevation, "date_openElevation": date_openElevation}, f)

# Function to update the request counter
def update_request_counter():
    today = date.today().isoformat()  # ✅ This correctly gets today's date
    today_date = date.today().isoformat()  # Get today's date in iso format
    today_month = date.today().month  # Get current month as an integer (1-12)
    count_openTopodata, date_openTopoData, count_openElevation, date_openElevation = load_counter()

    # Reset counter if the date has changed
    if date_openTopoData != today_date:
        count_openTopodata = 0
    
    if date_openElevation != today_month:
        count_openElevation = 0

    global api
    if api == 0:
        count_openTopodata += 1
    elif api == 1:
        count_openElevation += 1

    save_counter(count_openTopodata, today_date, count_openElevation,today_month)
    
    return count_openTopodata, count_openElevation  # Return the updated count

def send_api_request(addition = ""):
    
    global dataset
    request_count = update_request_counter()
    now = datetime.now()
    if api == 0:
        print(f"{now.hour:02d}:{now.minute:02d} | Fetching: {addition} | API Usage: {request_count} | {dataset}")
    elif api == 1:
        print(f"{now.hour:02d}:{now.minute:02d} | Fetching: {addition} | API Usage: {request_count}")
    elif api == 2:
        print(f"{now.hour:02d}:{now.minute:02d} | Fetching API")
    
if __name__ == "__main__":
    
    register()
    #unregister()


#--------------------------------------------------------------------------------------------------------------------
#DISPLAY GENERATION----------------------------------------------------------------------------------------------------------
#--------------------------------------------------------------------------------------------------------------------

import xml.etree.ElementTree as ET
from datetime import datetime
import bpy

def read_gpx_1_1(filepath):
    """
    Reads a GPX file and extracts the coordinates, elevation, and timestamps
    from either track points (trkpt) or route points (rtept).
    """

    tree = ET.parse(filepath)
    root = tree.getroot()

    segmentlist = []
    # Define namespaces for parsing GPX
    ns = {'default': 'http://www.topografix.com/GPX/1/1'}

    #find segments inside the file
    segments = root.findall('.//default:trkseg',ns)
    print(f"Segments: {len(segments)}")
    if segments:
        for seg in segments:
            # Try to find track points first
            points = seg.findall('.//default:trkpt', ns)
            point_type = 'trkpt'

            # If no track points found, look for route points
            if not points:
                points = seg.findall('.//default:rtept', ns)
                point_type = 'rtept'

            segcoords = []
            lowestElevation = 10000

            for pt in points:
                lat = float(pt.get('lat'))
                lon = float(pt.get('lon'))
                ele = pt.find('default:ele', ns)
                elevation = float(ele.text) if ele is not None else 0.0
                time = pt.find('default:time', ns)
                try:
                    timestamp = datetime.fromisoformat(time.text.replace("Z", "+00:00")) if time is not None else None
                except Exception:
                    timestamp = None
                segcoords.append((lat, lon, elevation, timestamp))
                if elevation < lowestElevation:
                    lowestElevation = elevation

            global elevationOffset
            elevationOffset = max(lowestElevation - 50, 0)

            bpy.context.scene.tp3d["sElevationOffset"] = elevationOffset
            bpy.context.scene.tp3d["o_verticesPath"] = f"{point_type.upper()}  Path vertices: {len(segcoords)}"
            segmentlist.append(segcoords)

    #coordinates.append(segcoords)
    return segmentlist





def read_gpx_1_0(filepath):
    """Reads a GPX 1.0 file and extracts the coordinates, elevation, and timestamps."""
    tree = ET.parse(filepath)
    root = tree.getroot()
    
    segmentlist = []
    # Define the namespace to handle the GPX 1.0 format correctly
    ns = {'gpx': 'http://www.topografix.com/GPX/1/0'}

    # Extract track points (latitude, longitude, elevation, timestamp)
    segcoords = []
    lowestElevation = 10000

    segments = root.findall('.//gpx:trkseg',ns)
    print(f"Segments in 1.0: {len(segments)}")
    
                        
    if segments:
        for seg in segments:
            # Extracting track points
            for trkpt in seg.findall('.//gpx:trkpt', ns):
                lat = float(trkpt.get('lat'))
                lon = float(trkpt.get('lon'))
                ele = trkpt.find('gpx:ele', ns)
                elevation = float(ele.text) if ele is not None else 0.0
                time = trkpt.find('gpx:time', ns)
                timestamp = datetime.fromisoformat(time.text) if time is not None else None
                #print(f"lat: {lat}, long: {lon}, ele: {elevation}, time: {timestamp}")
                segcoords.append((lat, lon, elevation, timestamp))
                
                if elevation < lowestElevation:
                    lowestElevation = elevation
            
            global elevationOffset
            elevationOffset = max(lowestElevation - 50, 0)

            bpy.context.scene.tp3d["sElevationOffset"] = elevationOffset
            
            bpy.context.scene.tp3d["o_verticesPath"] = f"Path vertices: {len(segcoords)}"
            segmentlist.append(segcoords)
            
    return segmentlist

def read_igc(filepath):
    """Reads an IGC file and extracts the coordinates, elevation, and timestamps."""
    segmentlist = []
    coordinates = []
    lowestElevation = 10000
    
    with open(filepath, 'r') as file:
        for line in file:
            # IGC B records contain position data
            if line.startswith('B'):
                try:
                    # Extract time (HHMMSS)
                    time_str = line[1:7]
                    hours = int(time_str[0:2])
                    minutes = int(time_str[2:4])
                    seconds = int(time_str[4:6])
                    
                    # Extract latitude (DDMMmmmN/S)
                    lat_str = line[7:15]
                    lat_deg = int(lat_str[0:2])
                    lat_min = int(lat_str[2:4])
                    lat_min_frac = int(lat_str[4:7]) / 1000.0
                    lat = lat_deg + (lat_min + lat_min_frac) / 60.0
                    if lat_str[7] == 'S':
                        lat = -lat
                    
                    # Extract longitude (DDDMMmmmE/W)
                    lon_str = line[15:24]
                    lon_deg = int(lon_str[0:3])
                    lon_min = int(lon_str[3:5])
                    lon_min_frac = int(lon_str[5:8]) / 1000.0
                    lon = lon_deg + (lon_min + lon_min_frac) / 60.0
                    if lon_str[8] == 'W':
                        lon = -lon
                    
                    # Extract pressure altitude (in meters)
                    pressure_alt = int(line[25:30])
                    
                    # Extract GPS altitude (in meters)
                    gps_alt = int(line[30:35])
                    
                    # Create timestamp (using current date since IGC files don't store date in B records)
                    now = datetime.now()
                    timestamp = datetime(now.year, now.month, now.day, hours, minutes, seconds)
                    
                    # Use GPS altitude for elevation
                    elevation = gps_alt
                    
                    coordinates.append((lat, lon, elevation, timestamp))
                    
                    if elevation < lowestElevation:
                        lowestElevation = elevation
                        
                except (ValueError, IndexError) as e:
                    print(f"Error parsing IGC line: {line.strip()}")
                    continue
    
    global elevationOffset
    elevationOffset = max(lowestElevation - 50, 0)
    
    bpy.context.scene.tp3d["o_verticesPath"] = "Path vertices: " + str(len(coordinates))

    segmentlist.append(coordinates)
    return segmentlist


def read_gpx_directory(directory_path):
    """Reads all GPX files in a directory and extracts coordinates, elevation, and timestamps."""
    
    # Define GPX namespace
    ns = {'default': 'http://www.topografix.com/GPX/1/1'}
    
    # List to store all coordinates from all GPX files
    coordinates = []
    coordinatesSeparate = []  # Stores a list of lists for separate files
    lowestElevation = 10000  # High initial value

    # Iterate over all files in the directory
    for filename in os.listdir(directory_path):
        if filename.lower().endswith(".gpx"):  # Only process .gpx files
            filepath = os.path.join(directory_path, filename)

            file_extension = os.path.splitext(filepath)[1].lower()
            if file_extension == '.gpx':
                tree = ET.parse(filepath)
                root = tree.getroot()
                version = root.get("version")
                print(f"File Name: {filename}, File Version: {version}")
                if version == "1.0":
                    co= read_gpx_1_0(filepath)
                if version == "1.1":
                    co= read_gpx_1_1(filepath)
            elif file_extension == '.igc':
                co= read_igc(filepath)

            # Append the file-specific list to coordinatesSeparate
            if co:
                for coseg in co:
                    coordinatesSeparate.append(coseg)
                    lowest = min(coseg, key = lambda x: x[2])
                    lowest_In_coords = lowest[2]
                    if lowest_In_coords < lowestElevation:
                        lowestElevation = lowest_In_coords
                        print(f"new Lowest Elevation: {lowestElevation}")
            
    #Merge the separate coordinates to one big list together
    coordinates = [pt for sublist in coordinatesSeparate for pt in sublist]
    

    # Calculate elevation offset
    global elevationOffset
    elevationOffset = max(lowestElevation - 50, 0)

    bpy.context.scene.tp3d["sElevationOffset"] = elevationOffset

    # Store the number of points in the Blender scene property
    bpy.context.scene.tp3d["o_verticesPath"] = f"Path vertices: {len(coordinates)}"
    
    print(f"Total GPX files processed: {len(coordinatesSeparate)}")
    
    return coordinatesSeparate

def read_gpx_file():

    coords = []
    file_extension = os.path.splitext(gpx_file_path)[1].lower()
    if file_extension == '.gpx':
        tree = ET.parse(gpx_file_path)
        root = tree.getroot()
        version = root.get("version")

        ns = {'default': root.tag.split('}')[0].strip('{')}
        global GPXsections
        GPXsections = len(root.findall(".//default:trkseg", ns))
        print(f"GPX Sections: {GPXsections}")
        
        if version == "1.0":
            coords = read_gpx_1_0(gpx_file_path)
        if version == "1.1":
            coords= read_gpx_1_1(gpx_file_path)
    elif file_extension == '.igc':
        coords= read_igc(gpx_file_path)
    else:
        show_message_box("不支持的文件格式。请使用.gpx或.igc文件。")
        toggle_console()
        return

    print(f"poats: {len(coords)}")
    
    return coords
    

# Load cache from disk
def load_elevation_cache():
    """Load the elevation cache from disk"""

    global _elevation_cache
    if os.path.exists(elevation_cache_file):
        try:
            with open(elevation_cache_file, "r") as f:
                _elevation_cache = json.load(f)
        except Exception as e:
            print(f"Error loading elevation cache: {str(e)}")
            _elevation_cache = {}
    else:
        _elevation_cache = {}

# Save cache to disk
def save_elevation_cache():
    """Save the elevation cache to disk"""
    # Limit cache size to prevent excessive file sizes
    print(f"Currently cached:  {len(_elevation_cache)}")
    if len(_elevation_cache) > cacheSize:
        # Keep only the most recent entries
        keys = list(_elevation_cache.keys())
        for key in keys[:-cacheSize]:
            del _elevation_cache[key]
            
    try:
        with open(elevation_cache_file, "w") as f:
            json.dump(_elevation_cache, f)
    except Exception as e:
        print(f"Error saving elevation cache: {str(e)}")

def get_cached_elevation(lat, lon, api_type="opentopodata"):
    """Get elevation from cache if available"""
    key = f"{lat:.5f}_{lon:.5f}_{api_type}"
    return _elevation_cache.get(key)

def cache_elevation(lat, lon, elevation, api_type="opentopodata"):
    """Cache elevation data"""
    key = f"{lat:.5f}_{lon:.5f}_{api_type}"
    _elevation_cache[key] = elevation

def setupColors():
    #Create or get green material
    mat_name = "BASE"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.05, 0.7, 0.05, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------
    #Create or get green material
    mat_name = "FOREST"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.05, 0.25, 0.05, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Gray material
    mat_name = "MOUNTAIN"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.5, 0.5, 0.5, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Blue material
    mat_name = "WATER"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.0, 0.0, 0.8, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Red material
    mat_name = "TRAIL"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (1.0, 0.0, 0.0, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------

    
    #Create or get Yellow material
    mat_name = "CITY"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.7, 0.7, 0.1, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------


    
    #Create or get Black material
    mat_name = "BLACK"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (0.0, 0.0, 0.0, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------
    

    
    #Create or get White material
    mat_name = "WHITE"
    if mat_name not in bpy.data.materials:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
    else:
        mat = bpy.data.materials[mat_name]

    nodes = mat.node_tree.nodes
    links = mat.node_tree.links

    # Find Principled BSDF by type
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)

    # If none exists, create one
    if not bsdf:
        bsdf = nodes.new(type="ShaderNodeBsdfPrincipled")
        bsdf.location = (0, 0)

    # Find Material Output
    output = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    if not output:
        output = nodes.new(type="ShaderNodeOutputMaterial")
        output.location = (300, 0)

    # Connect BSDF → Output
    if not bsdf.outputs["BSDF"].is_linked:
        links.new(bsdf.outputs["BSDF"], output.inputs["Surface"])
    
    # Set base color
    bsdf.inputs["Base Color"].default_value = (1.0, 1.0, 1.0, 1.0)
    
    #-------------------------------------------------------------------------------------------------------------------



def calculate_scale(mapSize, coordinates):
    
    #scalemode = bpy.context.scene.tp3d.get('scalemode',"SCALE")
    
    #for lat, lon, ele in coordinates:
    min_lat = min(point[0] for point in coordinates)
    max_lat = max(point[0] for point in coordinates)
    min_lon = min(point[1] for point in coordinates)
    max_lon = max(point[1] for point in coordinates)
    
    
    R = 6371  # Earth's radius in meters (Web Mercator standard)
    x1 = R * math.radians(min_lon)
    #x1 = R * math.radians(min_lon) * math.cos(math.radians(min_lat))
    y1 = R * math.log(math.tan(math.pi / 4 + math.radians(min_lat) / 2))
    x2 = R * math.radians(max_lon)
    #x2 = R * math.radians(max_lon) * math.cos(math.radians(max_lat))
    y2 = R * math.log(math.tan(math.pi / 4 + math.radians(max_lat) / 2))
    width = abs(x2 - x1)
    height = abs(y2 - y1)
    distance = math.sqrt((x2 - x1)**2 + (y2 - y1)**2)

    #COMMENTED OUT
    #CALCULATES THE ACCURATE SCALE BUT MULTIPLE PATHS TO EACH OTHER WONT ALIGN CORRECTLY WITH IT AS THE "mf"
    #IS DIFFRENT FOR EACH LATITUDE AND THEREFORE HAS A DIFFRENT "COORDINATE SYSTEM"
    if scalemode == "SCALE":
        mx1 = x1 = R * math.radians(min_lon) * math.cos(math.radians(min_lat))
        mx2 = x2 = R * math.radians(max_lon) * math.cos(math.radians(max_lat))
        mwidth = abs(mx1 - mx2)
        mf = 1/width * mwidth
        mf = 1
        print(f"mf: {mf}")

    if scalemode == "COORDINATES" or scalemode == "SCALE":
        distance = 0

    maxer = max(width,height, distance)

    print(f"maxer:{maxer}")
    scale = 1
    if scalemode == "COORDINATES" or type == 2 or type == 3:
        scale = mapSize / maxer
    elif scalemode == "FACTOR":
        scale = (mapSize * pathScale) / maxer
    elif scalemode == "SCALE":
        scale = pathScale * mf

    return scale

def convert_to_blender_coordinates(lat, lon, elevation, timestamp):
    """
    将GPS坐标转换为Blender 3D坐标系统
    
    坐标转换说明：
    - GPS使用经纬度（球面坐标系）
    - Blender使用XYZ（笛卡尔坐标系）
    - 需要考虑地球曲率和投影变形
    
    参数：
        lat (float): 纬度，范围-90到90度
        lon (float): 经度，范围-180到180度
        elevation (float): 海拔高度，单位米
        timestamp (str): 时间戳（用于轨迹时间信息）
    
    返回：
        tuple: (x, y, z, timestamp) Blender坐标系中的位置
    """

    scaleHor = bpy.context.scene.tp3d.sScaleHor

    
    R = 6371  # Earth's radius in meters (Web Mercator standard)
    x = R * math.radians(lon) * scaleHor
    y = R * math.log(math.tan(math.pi / 4 + math.radians(lat) / 2)) * scaleHor
    z = (elevation - elevationOffset) /1000 * scaleElevation * autoScale
    
    
    
    
    return (x, y, z)

# Convert offsets to latitude/longitude
def convert_to_geo(x,y):
    """Converts Blender x/y offsets to latitude/longitude."""

    scaleHor = bpy.context.scene.tp3d.sScaleHor
    
    R = 6371  # Earth's radius in meters (Web Mercator standard)
    longitude = math.degrees((x) / (R * scaleHor) )
    latitude = math.degrees(2 * math.atan(math.exp((y) / (R * scaleHor) )) - math.pi / 2)
    return latitude, longitude

def create_curve_from_coordinates(coordinates):
    """
    Create a curve in Blender based on a list of (x, y, z) coordinates.
    """
    # Create a new curve object
    curve_data = bpy.data.curves.new('GPX_Curve', type='CURVE')
    curve_data.dimensions = '3D'
    polyline = curve_data.splines.new('POLY')
    polyline.points.add(count=len(coordinates) - 1)

    # Populate the curve with points
    for i, coord in enumerate(coordinates):
        polyline.points[i].co = (coord[0], coord[1], coord[2], 1)  # (x, y, z, w)

    # Create an object with this curve
    curve_object = bpy.data.objects.new('GPX_Curve_Object', curve_data)
    bpy.context.collection.objects.link(curve_object)
    curve_object.data.bevel_depth = pathThickness/2  # Set the thickness of the curve
    curve_object.data.bevel_resolution = 4  # Set the resolution for smoothness
    
    mod = curve_object.modifiers.new(name="Remesh",type="REMESH")
    mod.mode = "VOXEL"
    mod.voxel_size = 0.05 * pathThickness * 10/2
    mod.adaptivity = 0.0
    curve_object.data.use_fill_caps = True
        
    curve_object.data.name = name + "_Trail"
    curve_object.name = name + "_Trail"
    
    
    curve_object.select_set(True)


    bpy.context.view_layer.objects.active = curve_object

    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.curve.select_all(action='SELECT')
    #bpy.ops.curve.smooth()
    bpy.ops.object.mode_set(mode='OBJECT')



    # Convert to mesh
    if shape == "HEXAGON INNER TEXT" or shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
        #bpy.ops.object.convert(target='MESH')
        pass

def simplify_curve(points_with_extra, min_distance=0.1000):
    """
    Removes points that are too close to any previously accepted point.
    Keeps the full (x, y, z, time) format.
    """

    if not points_with_extra:
        return []

    simplified = [points_with_extra[0]]
    last_xyz = Vector(points_with_extra[0][:3])
    skipped = 0

    for pt in points_with_extra[1:]:
        current_xyz = Vector(pt[:3])
        if (current_xyz - last_xyz).length >= min_distance:
            simplified.append(pt)
            last_xyz = current_xyz
        else:
            skipped += 1
            pass

    print(f"Smooth curve: Removed {skipped} vertices")
    return simplified

def create_hexagon(size):
    """Creates a hexagon at (0,0,0), subdivides it, and rotates it by 90 degrees."""
    global num_subdivisions
    verts = []
    faces = []

    for i in range(6):
        angle = math.radians(60 * i)
        x = size * math.cos(angle)
        y = size * math.sin(angle)
        verts.append((x, y, 0))
    verts.append((0, 0, 0))  # Center vertex
    faces = [[i, (i + 1) % 6, 6] for i in range(6)]
    mesh = bpy.data.meshes.new("Hexagon")
    obj = bpy.data.objects.new("Hexagon", mesh)
    bpy.context.collection.objects.link(obj)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    bpy.context.view_layer.objects.active = obj
    bpy.ops.object.mode_set(mode='EDIT')
    #bpy.ops.mesh.subdivide(number_cuts=num_subdivisions)
    for _ in range(num_subdivisions):
        bpy.ops.mesh.subdivide(number_cuts=1)  # 1 cut per loop for even refinement
    bpy.ops.object.mode_set(mode='OBJECT')
    obj.name = name
    obj.data.name = name
    return obj

def create_rectangle(width, height):
    """Creates a rectangle at (0,0,0), subdivides it, and rotates it by 90 degrees."""
    global num_subdivisions

    verts = [
        (-width / 2, -height / 2, 0),  # Bottom-left
        (width / 2, -height / 2, 0),   # Bottom-right
        (width / 2, height / 2, 0),    # Top-right
        (-width / 2, height / 2, 0)    # Top-left
    ]
    faces = [[0, 1, 2, 3]]
    mesh = bpy.data.meshes.new("Rectangle")
    obj = bpy.data.objects.new("Rectangle", mesh)
    bpy.context.collection.objects.link(obj)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    bpy.context.view_layer.objects.active = obj
    bpy.ops.object.mode_set(mode='EDIT')
    for _ in range(num_subdivisions):
        bpy.ops.mesh.subdivide(number_cuts=1)  # 1 cut per loop for even refinement
    #bpy.ops.mesh.subdivide(number_cuts=num_subdivisions)  # Can change number of subdivisions if needed
    bpy.ops.object.mode_set(mode='OBJECT')
    obj.name = name
    obj.data.name = name
    
    return obj



def create_circle(radius, num_segments=64):
    
    # Ensure we are in Object Mode
    try:
        bpy.ops.object.mode_set(mode='OBJECT')
    except:
        pass

    # Create a new mesh and object
    mesh = bpy.data.meshes.new(name)
    obj = bpy.data.objects.new(name, mesh)
    

    # Link object to the scene collection
    bpy.context.collection.objects.link(obj)

    # Generate circle vertices
    verts = []
    faces = []
    
    for i in range(num_segments):
        angle = math.radians(360 * i / num_segments)
        x = radius * math.cos(angle)
        y = radius * math.sin(angle)
        verts.append((x, y, 0))

    # Create edges between consecutive points
    edges = [(i, (i + 1) % num_segments) for i in range(num_segments)]

    # Create the mesh from data
    mesh.from_pydata(verts, edges, [])  # No center vertex, no faces yet
    mesh.update()

    # Make the object active and switch to Edit Mode
    bpy.context.view_layer.objects.active = obj
    bpy.ops.object.mode_set(mode='EDIT')

    # Select all vertices and fill the circle
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.fill_grid()
    
    #bpy.ops.mesh.subdivide(number_cuts=max(int(num_subdivisions/15),0))
    for _ in range(num_subdivisions):
        bpy.ops.mesh.subdivide(number_cuts=1)  # 1 cut per loop for even refinement

    # Switch back to Object Mode
    bpy.ops.object.mode_set(mode='OBJECT')

    return obj





# Get real elevation for a point
def get_elevation_single(lat, lon):
    """Fetches real elevation for a single latitude and longitude using OpenTopoData."""
    url = f"https://api.opentopodata.org/v1/{dataset}?locations={lat},{lon}"
    response = requests.get(url).json()
    elevation = response['results'][0]['elevation'] if 'results' in response else 0
    return elevation  # Scale down elevation to match Blender terrain


def get_elevation_openTopoData(coords, lenv = 0, pointsDone = 0):
    """Fetches real elevation for each vertex using OpenTopoData with request batching."""

    disableCache = bpy.context.scene.tp3d.get("disableCache",0)

    # Ensure the cache is loaded
    if not _elevation_cache:
        load_elevation_cache()

    # First, check which coordinates need fetching (not in cache)
    coords_to_fetch = []
    coords_indices = []

    elevations = [0] * len(coords)  # Pre-allocate list


    
    #check if coordinates are in cache or not
    for i, (lat, lon) in enumerate(coords):
        cached_elevation = get_cached_elevation(lat, lon)
        if cached_elevation is not None and disableCache == 0:
            # Use cached elevation
            elevations[i] = cached_elevation
        else:
            # Need to fetch this coordinate
            elevations[i] = -5
            coords_to_fetch.append((lat, lon))
            coords_indices.append(i)

    if len(coords) - len(coords_to_fetch) > 0:
        print(f"Using: {len(coords) - len(coords_to_fetch)} cached Coordinates")
    
    # If all elevations were found in cache, return immediately
    if not coords_to_fetch:
        return elevations
    
    #coords = [convert_to_geo(y, x, v[0], v[1]) for v in vertices]
    #elevations = []
    batch_size = 100
    for i in range(0, len(coords_to_fetch), batch_size):
        batch = coords_to_fetch[i:i + batch_size]
        query = "|".join([f"{c[0]},{c[1]}" for c in batch])
        url = f"{opentopoAdress}{dataset}?locations={query}"
        #print(url)
        last_request_time = time.monotonic()
        response = requests.get(url)
        nr = i + len(batch) + pointsDone
        addition = f" {nr}/{int(lenv)}"
        send_api_request(addition)
        response.raise_for_status()
        
        
        data = response.json()
        # Handle the elevation data and replace 'null' with 0
        for o, result in enumerate(data['results']):
            elevation = result.get('elevation', None)  # Safe get, default to None if key is missing
            if elevation is None:
                elevation = 0  # Replace None (null in JSON) with 0
            cache_elevation(batch[o][0], batch[o][1], elevation)
            ind = coords_indices[i+o]
            elevations[ind] = elevation
        
        # Get current time
        now = time.monotonic()  # Monotonic time is safer for measuring elapsed time
        elapsed_time = now - last_request_time
        if i + batch_size < len(coords_to_fetch) and elapsed_time < 1.3:
            time.sleep(1.3 - elapsed_time)  # Pause to prevent request throttling



    return elevations

def get_elevation_openElevation(coords, lenv = 0, pointsDone = 0):
    """Fetches real elevation for each vertex using Open-Elevation with request batching."""
    
    elevations = []
    batch_size = 1000
    for i in range(0, len(coords), batch_size):
        batch = coords[i:i + batch_size]
        # Open-Elevation expects a POST request with JSON body
        payload = {"locations": [{"latitude": c[0], "longitude": c[1]} for c in batch]}
        url = "https://api.open-elevation.com/api/v1/lookup"
        last_request_time = time.monotonic()
        
        headers = {'Content-Type': 'application/json'}
        nr = i + len(batch) + pointsDone
        addition = f" {nr}/{int(lenv)}"
        send_api_request(addition)
        
        response = requests.post(url, json=payload, headers=headers)
        
        #print(url)
        #print(payload)
        
        response.raise_for_status()

        data = response.json()
        
        
        # Handle the elevation data and replace 'null' with 0
        for result in data['results']:
            elevation = result.get('elevation', None)
            if elevation is None:
                elevation = 0
            elevations.append(elevation)
        
        # Get current time for request rate limiting
        now = time.monotonic()  
        elapsed_time = now - last_request_time
        if elapsed_time < 2:
            time.sleep(2 - elapsed_time)  # Pause to prevent request throttling

    return elevations

def lonlat_to_tilexy(lon, lat, zoom):
    lat_rad = math.radians(lat)
    n = 2.0 ** zoom
    xtile = int((lon + 180.0) / 360.0 * n)
    ytile = int((1.0 - math.log(math.tan(lat_rad) + 1.0 / math.cos(lat_rad)) / math.pi) / 2.0 * n)
    return xtile, ytile

def lonlat_to_pixelxy(lon, lat, zoom):
    lat_rad = math.radians(lat)
    n = 2.0 ** zoom
    x = (lon + 180.0) / 360.0 * n * 256
    y = (1.0 - math.log(math.tan(lat_rad) + 1.0 / math.cos(lat_rad)) / math.pi) / 2.0 * n * 256
    return int(x % 256), int(y % 256)

def fetch_terrarium_tile_raw(zoom, xtile, ytile):
    """Fetch the raw PNG binary data for a tile, either from cache or online."""
    tile_path = os.path.join(terrarium_cache_dir, f"{zoom}_{xtile}_{ytile}.png")
    if not os.path.exists(tile_path):
        url = f"https://elevation-tiles-prod.s3.amazonaws.com/terrarium/{zoom}/{xtile}/{ytile}.png"
        #print("Sending Request")
        response = requests.get(url)
        response.raise_for_status()
        with open(tile_path, "wb") as f:
            f.write(response.content)
    with open(tile_path, "rb") as f:
        return f.read()

def paeth_predictor(a, b, c):
    # PNG Paeth filter
    p = a + b - c
    pa = abs(p - a)
    pb = abs(p - b)
    pc = abs(p - c)
    if pa <= pb and pa <= pc:
        return a
    elif pb <= pc:
        return b
    else:
        return c

def parse_png_rgb_data(png_bytes):
    """Extract uncompressed RGB bytes from a PNG image (supports all PNG filter types)."""
    assert png_bytes[:8] == b'\x89PNG\r\n\x1a\n', "Not a valid PNG file"
    offset = 8
    width = height = None
    idat_data = b''

    while offset < len(png_bytes):
        length = struct.unpack(">I", png_bytes[offset:offset+4])[0]
        chunk_type = png_bytes[offset+4:offset+8]
        data = png_bytes[offset+8:offset+8+length]
        offset += 12 + length

        if chunk_type == b'IHDR':
            width, height, bit_depth, color_type, _, _, _ = struct.unpack(">IIBBBBB", data)
            assert bit_depth == 8 and color_type == 2, "Only 8-bit RGB PNGs supported"
        elif chunk_type == b'IDAT':
            idat_data += data
        elif chunk_type == b'IEND':
            break

    raw = zlib.decompress(idat_data)
    stride = 3 * width
    rgb_array = []
    prev_row = bytearray(stride)

    for y in range(height):
        i = y * (stride + 1)
        filter_type = raw[i]
        scanline = bytearray(raw[i + 1:i + 1 + stride])
        recon = bytearray(stride)

        if filter_type == 0:
            recon[:] = scanline
        elif filter_type == 1:  # Sub
            for i in range(stride):
                val = scanline[i]
                left = recon[i - 3] if i >= 3 else 0
                recon[i] = (val + left) % 256
        elif filter_type == 2:  # Up
            for i in range(stride):
                recon[i] = (scanline[i] + prev_row[i]) % 256
        elif filter_type == 3:  # Average
            for i in range(stride):
                left = recon[i - 3] if i >= 3 else 0
                up = prev_row[i]
                recon[i] = (scanline[i] + (left + up) // 2) % 256
        elif filter_type == 4:  # Paeth
            for i in range(stride):
                a = recon[i - 3] if i >= 3 else 0
                b = prev_row[i]
                c = prev_row[i - 3] if i >= 3 else 0
                recon[i] = (scanline[i] + paeth_predictor(a, b, c)) % 256
        else:
            raise ValueError(f"Unsupported filter type {filter_type}")

        # Convert scanline to list of (R, G, B) tuples
        row = [(recon[i], recon[i+1], recon[i+2]) for i in range(0, stride, 3)]
        rgb_array.append(row)
        prev_row = recon

    return rgb_array


def terrarium_pixel_to_elevation(r, g, b):
    """Convert Terrarium RGB pixel to elevation in meters."""
    return (r * 256 + g + b / 256) - 32768

def get_elevation_TerrainTiles(coords, lenv=0, pointsDone=0, zoom=10):

    #Each Tile requested is a PNG that is 256x256 Pixels big

    realdist1 = haversine(minLat,minLon,minLat,maxLon)*1000
    realdist2 = haversine(maxLat,minLon,maxLat,maxLon)*1000

    #calculating zoom
    zoom = 10
    horVerts = 1 + 2**(num_subdivisions+1)
    dist = 25.00000 / 2**(num_subdivisions-1) #25 is the rough distance between verts on resolution 1
    strt = 156543 #m/Pixel on Tile PNG
    #print(f"dist:{dist}")
    cntr = 2

    #print(f"scaleHor: {scaleHor}")
    vertdist = max(realdist1,realdist2)/horVerts #Distance between 2 vertices
    while strt > vertdist:
        cntr += 1
        strt /= 2
        #print(f"halved: {strt:.2f}, {cntr}, {vertdist:.2f}")
    #Max zoom level to 14
    cntr = min(cntr,15)

    #print(f"horVerts: {horVerts}")
    print(f"Zoom Level for API: {cntr}, Start fetching Data...")
        #print(f"calculated distance: {dist}")
    zoom = cntr
    
    
    


    tile_dict = {}
    for idx, (lat, lon) in enumerate(coords):
        xtile, ytile = lonlat_to_tilexy(lon, lat, zoom)
        tile_dict.setdefault((xtile, ytile), []).append((idx, lat, lon))

    total_tiles = len(tile_dict)
    progress_intervals = set(range(10,101,10))
    elevations = [0] * len(coords)
    for i, ((xtile, ytile), idx_lat_lon_list) in enumerate(tile_dict.items(), 1):
        percent_complete = int((i/ total_tiles) * 100)
        if percent_complete in progress_intervals:
            print(f"{datetime.now().strftime('%H:%M:%S')} - {percent_complete}% complete, {i}")
            progress_intervals.remove(percent_complete)
        try:
            png_bytes = fetch_terrarium_tile_raw(zoom, xtile, ytile)
            rgb_array = parse_png_rgb_data(png_bytes)
        except Exception as e:
            print(f"Failed to fetch or parse tile {zoom}/{xtile}/{ytile}: {e}")
            for idx, _, _ in idx_lat_lon_list:
                elevations[idx] = 0
            continue

        for idx, lat, lon in idx_lat_lon_list:
            px, py = lonlat_to_pixelxy(lon, lat, zoom)
            px = min(max(px, 0), 255)
            py = min(max(py, 0), 255)
            r, g, b = rgb_array[py][px]
            elevations[idx] = terrarium_pixel_to_elevation(r, g, b)

    return elevations

def get_elevation_path_openElevation(vertices):
    """Fetches real elevation for each vertex using OpenTopoData with request batching."""
    v = vertices
    coords = [(v[0], v[1], v[2], v[3]) for v in vertices]
    elevations = []
    batch_size = 1000
    for i in range(0, len(coords), batch_size):
        batch = coords[i:i + batch_size]
        # Open-Elevation expects a POST request with JSON body
        payload = {"locations": [{"latitude": c[0], "longitude": c[1]} for c in batch]}
        url = "https://api.open-elevation.com/api/v1/lookup"
        last_request_time = time.monotonic()
        
        headers = {'Content-Type': 'application/json'}

        addition = f"(overwrite path) {i + len(batch)}/{len(coords)}"
        send_api_request(addition)

        response = requests.post(url, json=payload, headers=headers)
        
        #print(url)
        #print(payload)
        
        response.raise_for_status()

        data = response.json()
        
        elevations.extend([r['elevation'] for r in data['results']])
        now = time.monotonic()  # Monotonic time is safer for measuring elapsed time
        elapsed_time = now - last_request_time
        if i + batch_size < len(coords) and elapsed_time < 1.4:
            time.sleep(1.4 - elapsed_time)  # Pause to prevent request throttling
    
    for i in range(len(vertices)):
        coords[i] =  (coords[i][0], coords[i][1], elevations[i], coords[i][3])
        #print(elevations[i])
    
    return coords
# Get real elevation for each vertex

def get_elevation_path_openTopoData(vertices):
    """Fetches real elevation for each vertex using OpenTopoData with request batching."""
    v = vertices
    coords = [(v[0], v[1], v[2], v[3]) for v in vertices]
    elevations = []
    batch_size = 100
    for i in range(0, len(coords), batch_size):
        batch = coords[i:i + batch_size]
        query = "|".join([f"{c[0]},{c[1]}" for c in batch])
        url = f"{opentopoAdress}{dataset}?locations={query}"
        last_request_time = time.monotonic()
        response = requests.get(url).json()
        addition = f"(overwrite path) {i + len(batch)}/{len(coords)}"
        send_api_request(addition)
        
        #elevations.extend([r['elevation'] for r in response['results']])
        elevations.extend([r.get('elevation') or 0 for r in response['results']])

        now = time.monotonic()  # Monotonic time is safer for measuring elapsed time
        elapsed_time = now - last_request_time
        if i + batch_size < len(coords) and elapsed_time < 1.4:
            time.sleep(1.4 - elapsed_time)  # Pause to prevent request throttling
    
    for i in range(len(vertices)):
        coords[i] =  (coords[i][0], coords[i][1], elevations[i], coords[i][3])
        #print(elevations[i])
    
    return coords

def RaycastCurveToMesh(curve_obj, mesh_obj):

    #MOVE EVERY POINT UP BY 100 SO ITS POSSIBLE TO RAYCAST IT DOWNARDS ONTO THE MESH
    offset = Vector((0, 0, 100))
    for spline in curve_obj.data.splines:
        if spline.type == 'BEZIER':
            for p in spline.bezier_points:
                p.co += offset
                # if you want to move the handles too:
                p.handle_left += offset
                p.handle_right += offset
        else:  # POLY / NURBS
            for p in spline.points:
                p.co = (p.co.x, p.co.y, p.co.z + offset.z, p.co.w)


        
    depsgraph = bpy.context.evaluated_depsgraph_get()
    eval_mesh_obj = mesh_obj.evaluated_get(depsgraph)

    curve_world     = curve_obj.matrix_world
    curve_world_inv = curve_world.inverted()

    mesh_world     = eval_mesh_obj.matrix_world
    mesh_world_inv = mesh_world.inverted()

    direction_world = Vector((0, 0, -1))  # world -Z
    direction_local = (mesh_world_inv.to_3x3() @ direction_world).normalized()

    for spline in curve_obj.data.splines:
        if spline.type == 'BEZIER':
            points = spline.bezier_points
        else:
            points = spline.points

        for point in points:
            # world-space position of curve point
            if spline.type == 'BEZIER':
                co_world = curve_world @ point.co
            else:
                co_world = curve_world @ point.co.xyz

            # convert origin to mesh local
            co_local = mesh_world_inv @ co_world

            # raycast in mesh local space
            success, hit_loc, normal, face_index = eval_mesh_obj.ray_cast(co_local, direction_local)

            if success:
                # back to world space
                hit_world = mesh_world @ hit_loc
                # then into curve local
                local_hit = curve_world_inv @ hit_world

                if spline.type == 'BEZIER':
                    point.co = local_hit
                    point.handle_left_type = point.handle_right_type = 'AUTO'
                else:
                    point.co = (local_hit.x, local_hit.y, local_hit.z, 1.0)
    
    bpy.context.view_layer.objects.active = curve_obj
    bpy.ops.object.mode_set(mode='EDIT')

    # select all points if you want to smooth everything
    bpy.ops.curve.select_all(action='SELECT')

    # run the smooth operator
    bpy.ops.curve.smooth()

    # back to Object Mode if you like
    bpy.ops.object.mode_set(mode='OBJECT')
                    

# Get tile elevation
def get_tile_elevation(obj):

    mesh = obj.data
    global api
    api = bpy.context.scene.tp3d.get('api',2)


    # Set chunk size based on API
    if api == 0 or api == 1:
        chunk_size = 100000
    elif api == 2:
        chunk_size = 50000000
    else:
        chunk_size = 100000  # fallback

    vertices = list(mesh.vertices)
    obj_matrix = obj.matrix_world

    # Convert all vertex positions to world space
    world_verts = [obj_matrix @ v.co for v in vertices]

    # Get min/max bounds in world space
    min_x = min(v.x for v in world_verts)
    max_x = max(v.x for v in world_verts)
    min_y = min(v.y for v in world_verts)
    max_y = max(v.y for v in world_verts)

    global minLon, maxLon, minLat, maxLat

    # Use object's world location as reference origin
    origin_lat = obj_matrix.translation.y
    origin_lon = obj_matrix.translation.x

    minl = convert_to_geo(min_x, min_y)
    maxl = convert_to_geo(max_x, max_y)

    minLat = minl[0]
    maxLat = maxl[0]
    minLon = minl[1]
    maxLon = maxl[1]


    realdist1 = haversine(minLat,minLon,minLat,maxLon)*1
    realdist2 = haversine(maxLat,minLon,maxLat,maxLon)*1
    bpy.context.scene.tp3d["sMapInKm"] = max(realdist1,realdist2)

    elevations = []
    for i in range(0, len(world_verts), chunk_size):
        chunk = world_verts[i:i + chunk_size]

        coords = [convert_to_geo(v.x, v.y) for v in chunk]

        if api == 0:
            chunk_elevations = get_elevation_openTopoData(coords, len(vertices), i)
        elif api == 1:
            chunk_elevations = get_elevation_openElevation(coords, len(vertices), i)
        elif api == 2:
            #print(f"Loading {i}/{len(vertices)}")
            chunk_elevations = get_elevation_TerrainTiles(coords, len(vertices), i)
        else:
            chunk_elevations = [0.0] * len(chunk)  # fallback

        elevations.extend(chunk_elevations)

        # Free memory after processing chunk
        del chunk_elevations

    save_elevation_cache()

    global lowestZ
    global highestZ
    lowestZ = min(elevations)
    highestZ = max(elevations)
    global additionalExtrusion
    additionalExtrusion = lowestZ
    diff = highestZ - lowestZ

    bpy.context.scene.tp3d["o_verticesMap"] = str(len(mesh.vertices))

    return elevations, diff

# Transform MapObject
def transform_MapObject(obj, newX, newY):
    obj.location.x += newX
    obj.location.y += newY

def haversine(lat1, lon1, lat2, lon2):
    """Calculates the great-circle distance between two points using the Haversine formula."""
    R = 6371.0  # Earth radius in kilometers
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    delta_phi = math.radians(lat2 - lat1)
    delta_lambda = math.radians(lon2 - lon1)

    a = math.sin(delta_phi / 2)**2 + math.cos(phi1) * math.cos(phi2) * math.sin(delta_lambda / 2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    distance = R * c  # distance in kilometers
    #print(f"Distance between 2 points: {distance}")
    return distance
    
    
def calculate_total_length(points):
    #Calculates the total path length in kilometers.
    total_distance = 0.0
    for i in range(1, len(points)):
        lon1, lat1, _, _ = points[i - 1]
        lon2, lat2, _, _ = points[i]
        total_distance += haversine(lon1, lat1, lon2, lat2)
    return total_distance

def calculate_total_elevation(points):
    #Calculates the total elevation gain in meters.
    total_elevation = 0.0
    for i in range(1, len(points)):
        _, _, elev1, _ = points[i - 1]
        _, _, elev2, _ = points[i]
        if elev2 > elev1:
            total_elevation += elev2 - elev1
    return total_elevation

def calculate_total_time(points):
    hrs = 0
    #Calculates the total time taken between the first and last points.
    if len(points) < 2:
        return 0.0
    start_time = points[0][3]
    end_time = points[-1][3]
    if start_time != None and end_time != None:
        time_diff = end_time - start_time
        hours = int(time_diff.total_seconds() / 3600)
        minutes = int((time_diff.total_seconds() / 3600 - hours) * 60)
        time_str = f"{hours}h {minutes}m"
        #print(time_str)
        hrs = time_diff.total_seconds() / 3600
    
    return hrs

def update_text_object(obj_name, new_text):
    """Updates the text of a Blender text object."""
    text_obj = bpy.data.objects.get(obj_name)
    if text_obj and text_obj.type == 'FONT':
        text_obj.data.body = new_text

def create_flag(name, position, flag_type="START", height=5, flag_width=3):
    """
    创建旗帜标记（起点或终点）
    
    功能说明：
    - 在指定位置创建3D旗帜模型
    - 包含旗杆、三角形旗面和底部插入座
    - 起点旗帜为绿色，终点旗帜为红色
    - 底部设计为可插入底板的结构（圆柱+底座）
    
    参数：
        name (str): 旗帜对象的名称
        position (tuple): 旗帜位置 (x, y, z)
        flag_type (str): 旗帜类型 "START" 或 "FINISH"
        height (float): 旗杆高度（毫米）
        flag_width (float): 旗面宽度（毫米）
    
    返回：
        object: 创建的旗帜对象
    """
    
    # 设计参数
    pole_radius = 0.4        # 旗杆半径
    insert_depth = 2.0       # 插入深度
    base_radius = 0.8        # 底座半径（比旗杆粗，便于固定）
    base_height = 0.5        # 底座高度
    
    # 1. 创建旗杆主体（从底座顶部到顶部）
    bpy.ops.mesh.primitive_cylinder_add(
        radius=pole_radius,
        depth=height,
        location=(position[0], position[1], position[2] + height/2)
    )
    pole = bpy.context.active_object
    pole.name = f"{name}_Pole"
    
    # 2. 创建插入部分（在底板下方）
    bpy.ops.mesh.primitive_cylinder_add(
        radius=pole_radius * 0.9,  # 略细，便于插入
        depth=insert_depth,
        location=(position[0], position[1], position[2] - insert_depth/2)
    )
    insert_part = bpy.context.active_object
    insert_part.name = f"{name}_Insert"
    
    # 3. 创建底座（在地表，便于固定和打印）
    bpy.ops.mesh.primitive_cylinder_add(
        radius=base_radius,
        depth=base_height,
        location=(position[0], position[1], position[2] + base_height/2)
    )
    base = bpy.context.active_object
    base.name = f"{name}_Base"
    
    # 4. 创建旗面（三角形）
    flag_height = flag_width * 0.6  # 旗面高度为宽度的60%
    
    # 定义三角形旗面的顶点
    verts = [
        (0, 0, 0),                      # 左下角（靠近旗杆）
        (flag_width, flag_height/2, 0), # 右边中点（旗面尖端）
        (0, flag_height, 0)             # 左上角（靠近旗杆）
    ]
    
    # 定义面
    faces = [(0, 1, 2)]
    
    # 创建网格
    mesh = bpy.data.meshes.new(f"{name}_Flag_Mesh")
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    
    # 创建对象
    flag = bpy.data.objects.new(f"{name}_Flag", mesh)
    bpy.context.collection.objects.link(flag)
    
    # 定位旗面（在旗杆顶部）
    flag.location = (
        position[0] + pole_radius,  # 紧贴旗杆边缘
        position[1],
        position[2] + height - flag_height/2
    )
    
    # 旋转旗面使其垂直
    flag.rotation_euler = (math.radians(90), 0, 0)
    
    # 设置材质颜色
    if flag_type == "START":
        # 起点：绿色
        color = (0.0, 0.8, 0.0, 1.0)  # RGBA
        mat_name = "FLAG_START"
    else:  # FINISH
        # 终点：红色
        color = (0.9, 0.0, 0.0, 1.0)  # RGBA
        mat_name = "FLAG_FINISH"
    
    # 创建或获取材质
    mat = bpy.data.materials.get(mat_name)
    if mat is None:
        mat = bpy.data.materials.new(name=mat_name)
        mat.use_nodes = True
        nodes = mat.node_tree.nodes
        bsdf = nodes.get("Principled BSDF")
        if bsdf:
            bsdf.inputs["Base Color"].default_value = color
            bsdf.inputs["Metallic"].default_value = 0.0
            bsdf.inputs["Roughness"].default_value = 0.5
    
    # 应用材质到旗面
    if flag.data.materials:
        flag.data.materials[0] = mat
    else:
        flag.data.materials.append(mat)
    
    # 为旗杆设置灰色材质
    pole_mat = bpy.data.materials.get("FLAG_POLE")
    if pole_mat is None:
        pole_mat = bpy.data.materials.new(name="FLAG_POLE")
        pole_mat.use_nodes = True
        nodes = pole_mat.node_tree.nodes
        bsdf = nodes.get("Principled BSDF")
        if bsdf:
            bsdf.inputs["Base Color"].default_value = (0.3, 0.3, 0.3, 1.0)
            bsdf.inputs["Metallic"].default_value = 0.8
            bsdf.inputs["Roughness"].default_value = 0.2
    
    if pole.data.materials:
        pole.data.materials[0] = pole_mat
    else:
        pole.data.materials.append(pole_mat)
    
    # 为插入部分应用相同的旗杆材质
    if insert_part.data.materials:
        insert_part.data.materials[0] = pole_mat
    else:
        insert_part.data.materials.append(pole_mat)
    
    # 为底座应用旗杆材质
    if base.data.materials:
        base.data.materials[0] = pole_mat
    else:
        base.data.materials.append(pole_mat)
    
    # 合并所有部分：旗杆 + 插入部分 + 底座 + 旗面
    bpy.ops.object.select_all(action='DESELECT')
    pole.select_set(True)
    insert_part.select_set(True)
    base.select_set(True)
    flag.select_set(True)
    bpy.context.view_layer.objects.active = pole
    bpy.ops.object.join()
    
    combined_flag = bpy.context.active_object
    combined_flag.name = name
    
    # 添加自定义属性标记
    combined_flag["Object type"] = "FLAG"
    combined_flag["Flag Type"] = flag_type
    combined_flag["Addon"] = "TrailPrint3D"
    
    print(f"✓ 创建{flag_type}旗帜于位置: ({position[0]:.2f}, {position[1]:.2f}, {position[2]:.2f})")
    
    return combined_flag

def find_elevation_extremes(obj):
    """
    查找网格上海拔最高和最低的点
    
    参数：
        obj: Blender网格对象
    
    返回：
        tuple: ((min_x, min_y, min_z), (max_x, max_y, max_z))
               最低点坐标和最高点坐标
    """
    if obj.type != 'MESH':
        return None, None
    
    mesh = obj.data
    
    # 获取世界坐标系中的顶点位置
    matrix_world = obj.matrix_world
    
    min_z = float('inf')
    max_z = float('-inf')
    min_point = None
    max_point = None
    
    for vert in mesh.vertices:
        # 转换到世界坐标
        world_co = matrix_world @ vert.co
        
        if world_co.z < min_z:
            min_z = world_co.z
            min_point = (world_co.x, world_co.y, world_co.z)
        
        if world_co.z > max_z:
            max_z = world_co.z
            max_point = (world_co.x, world_co.y, world_co.z)
    
    print(f"地形分析: 最低点海拔={min_z:.2f}mm, 最高点海拔={max_z:.2f}mm, 高度差={max_z-min_z:.2f}mm")
    
    return min_point, max_point

def find_path_endpoints(curve_obj):
    """
    查找路径曲线的起点和终点
    
    参数：
        curve_obj: Blender曲线对象
    
    返回：
        tuple: (start_point, end_point) - 起点和终点的世界坐标
    """
    if curve_obj is None or curve_obj.type != 'CURVE':
        print("错误: 提供的对象不是有效的曲线对象")
        return None, None
    
    curve_data = curve_obj.data
    matrix_world = curve_obj.matrix_world
    
    # 获取第一条样条线
    if len(curve_data.splines) == 0:
        print("错误: 曲线没有样条线")
        return None, None
    
    spline = curve_data.splines[0]
    
    # 获取起点和终点
    if len(spline.points) > 0:
        # NURBS曲线
        start_local = spline.points[0].co[:3]
        end_local = spline.points[-1].co[:3]
    elif len(spline.bezier_points) > 0:
        # Bezier曲线
        start_local = spline.bezier_points[0].co
        end_local = spline.bezier_points[-1].co
    else:
        print("错误: 样条线没有点")
        return None, None
    
    # 转换到世界坐标
    start_world = matrix_world @ Vector(start_local)
    end_world = matrix_world @ Vector(end_local)
    
    start_point = (start_world.x, start_world.y, start_world.z)
    end_point = (end_world.x, end_world.y, end_world.z)
    
    print(f"路径分析: 起点=({start_point[0]:.2f}, {start_point[1]:.2f}, {start_point[2]:.2f})")
    print(f"路径分析: 终点=({end_point[0]:.2f}, {end_point[1]:.2f}, {end_point[2]:.2f})")
    
    return start_point, end_point

def fix_mesh_anomalies(obj, threshold=0.1):
    """
    修复网格中的异常点
    - 删除孤立的顶点
    - 修复非流形边
    - 平滑异常的尖刺
    """
    if obj.type != 'MESH':
        return
    
    bpy.context.view_layer.objects.active = obj
    bpy.ops.object.mode_set(mode='EDIT')
    
    # 获取网格数据
    bm = bmesh.from_edit_mesh(obj.data)
    
    # 1. 删除孤立的顶点
    isolated_verts = [v for v in bm.verts if not v.link_edges]
    if isolated_verts:
        bmesh.ops.delete(bm, geom=isolated_verts, context='VERTS')
        print(f"删除了 {len(isolated_verts)} 个孤立顶点")
    
    # 2. 删除重复的顶点
    bmesh.ops.remove_doubles(bm, verts=bm.verts, dist=threshold * 0.01)
    
    # 3. 检测并修复异常高的顶点（相对于邻近顶点）
    fixed_count = 0
    for v in bm.verts:
        if len(v.link_edges) > 0:
            # 计算相邻顶点的平均Z值
            neighbor_z = []
            for edge in v.link_edges:
                other_vert = edge.other_vert(v)
                neighbor_z.append(other_vert.co.z)
            
            if neighbor_z:
                avg_z = sum(neighbor_z) / len(neighbor_z)
                # 如果当前顶点的Z值与邻近顶点的平均值相差太大，则修正它
                if abs(v.co.z - avg_z) > threshold * 10:
                    v.co.z = avg_z
                    fixed_count += 1
    
    if fixed_count > 0:
        print(f"修复了 {fixed_count} 个异常点")
    
    # 4. 重新计算法线
    bmesh.ops.recalc_face_normals(bm, faces=bm.faces)
    
    # 更新网格
    bmesh.update_edit_mesh(obj.data)
    bm.free()
    
    bpy.ops.object.mode_set(mode='OBJECT')
    
    # 5. 应用平滑修改器来平滑表面
    smooth_mod = obj.modifiers.new(name="Smooth", type='SMOOTH')
    smooth_mod.iterations = 2
    smooth_mod.factor = 0.5
    bpy.context.view_layer.objects.active = obj
    bpy.ops.object.modifier_apply(modifier=smooth_mod.name)
    
    print(f"网格修复完成: {obj.name}")
        
def export_to_STL(zobj):
    
    exportPath = bpy.context.scene.tp3d.get('export_path', None)
    bpy.ops.object.select_all(action='DESELECT')
    zobj.select_set(True)
    bpy.context.view_layer.objects.active = zobj

    if zobj.material_slots:  
        bpy.ops.wm.obj_export(filepath=exportPath + zobj.name + ".obj",
            export_selected_objects=True,
            export_triangulated_mesh=True, 
            apply_modifiers=True,
            export_materials=True,
            forward_axis="Y",
            up_axis="Z",
            )
        #show_message_box("File Exported as OBJ because it contains Materials","INFO","OBJ File Exported")
    else:
        bpy.ops.wm.stl_export(filepath=exportPath +  zobj.name + ".stl", export_selected_objects = True)
        #show_message_box("File Exported to your selected directory","INFO","File Exported")
    
    zobj.select_set(False)  # Select the object

def export_selected_to_STL():

    exportPath = bpy.context.scene.tp3d.get('export_path', None)
    selected_objects = bpy.context.selected_objects
    active_obj = bpy.context.active_object

    if not selected_objects:
            show_message_box("未选择任何对象")
            return('CANCELLED')

    for zobj in selected_objects:
        bpy.ops.object.select_all(action='DESELECT')
        zobj.select_set(True)
        bpy.context.view_layer.objects.active = zobj

        if zobj.material_slots:  
            bpy.ops.wm.obj_export(filepath=exportPath + zobj.name + ".obj",
                export_selected_objects=True,
                export_triangulated_mesh=True, 
                apply_modifiers=True,
                export_materials=True,
                forward_axis="Y",
                up_axis="Z",
                )
            #show_message_box("File Exported as OBJ because it contains Materials","INFO","OBJ File Exported")
            show_message_box("File Exported to your selected directory","INFO","File Exported")
        else:
            bpy.ops.wm.stl_export(filepath=exportPath +  zobj.name + ".stl", export_selected_objects = True)
            show_message_box("File Exported to your selected directory","INFO","File Exported")


    bpy.ops.object.select_all(action='DESELECT')
    for zobj in selected_objects:
        zobj.select_set(True)
    bpy.context.view_layer.objects.active = active_obj     


    active_obj = bpy.context.active_object





def zoom_camera_to_selected(obj):
    
    bpy.ops.object.select_all(action='DESELECT')
    
    obj.select_set(True)  # Select the object
    
    area = [area for area in bpy.context.screen.areas if area.type == "VIEW_3D"][0]
    region = area.regions[-1]

    with bpy.context.temp_override(area=area, region=region):
        bpy.ops.view3d.view_selected(use_all_regions=False)
        
        
def create_text(name, text, position, scale_multiplier, rotation=(0, 0, 0), extrude=20):
    txt_data = bpy.data.curves.new(name=name, type='FONT')
    txt_obj = bpy.data.objects.new(name=name, object_data=txt_data)
    bpy.context.collection.objects.link(txt_obj)
    
    global textFont

    # 如果未指定字体，自动查找系统中文字体
    if textFont == "":
        textFont = get_chinese_font()
        
        # 如果没有找到中文字体，使用系统默认英文字体作为备用
        if textFont == "":
            if platform.system() == "Windows":
                textFont = "C:/WINDOWS/FONTS/ariblk.ttf"  # Windows默认粗体
            elif platform.system() == "Darwin":
                textFont = "/System/Library/Fonts/Supplemental/Arial Black.ttf"  # macOS默认粗体
            else:
                textFont = ""  # Linux系统使用Blender内置字体

    # 设置文本内容和挤出厚度
    txt_data.body = text
    txt_data.extrude = extrude
    
    # 尝试加载指定的字体文件
    try:
        if textFont != "":
            txt_data.font = bpy.data.fonts.load(textFont)
    except Exception as e:
        print(f"加载字体失败: {e}，使用Blender默认字体")
        # 如果加载失败，Blender会自动使用内置的默认字体
    txt_data.align_x = 'CENTER'
    txt_data.align_y = "CENTER"
    
    txt_obj.scale = (scale_multiplier, scale_multiplier, 1)
    txt_obj.location = position
    txt_obj.rotation_euler = rotation
    
    txt_obj.location.z -= 1
    
    return txt_obj

def HexagonInnerText():
    
    global total_elevation
    global total_length

    textSize = bpy.context.scene.tp3d.textSize
    textSize2 = bpy.context.scene.tp3d.textSizeTitle

    if textSize2 == 0:
        textSize2 = textSize
    
    
    
    dist =  (size/2 - size/2 * (1-pathScale)/2)
    
    temp_y = math.sin(math.radians(90)) * (dist  * math.cos(math.radians(30)))
    

    
    tName = create_text("t_name", "Name", (0, temp_y, 0.1),1)

    
    for i, (text_name, angle) in enumerate(zip(["t_length", "t_elevation", "t_duration"], [210, 270, 330])):
        angle_centered = angle + 90
        x = math.cos(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        y = math.sin(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        rot_z = math.radians(angle_centered)
        create_text(text_name, text_name.split("_")[1].capitalize(), (x, y, 0.1),1,  (0, 0, rot_z), 100)
    
    tElevation = bpy.data.objects.get("t_elevation")
    tLength = bpy.data.objects.get("t_length")
    tDuration = bpy.data.objects.get("t_duration")
    

    
    transform_MapObject(tName, centerx, centery)
    transform_MapObject(tElevation, centerx, centery)
    transform_MapObject(tLength, centerx, centery)
    transform_MapObject(tDuration, centerx, centery)
    

    update_text_object("t_name", f"{name}")
    update_text_object("t_elevation", f"{total_elevation:.2f} hm")
    update_text_object("t_length", f"{total_length:.2f} km")
    update_text_object("t_duration", f"{time_str}")

    if overwriteLength != "":
        update_text_object("t_length", overwriteLength)
    if overwriteHeight != "":
        update_text_object("t_elevation", overwriteHeight)
    if overwriteTime != "":
        update_text_object("t_duration", overwriteTime)
    
    #Scale text sizes to mm values (blender units)
    bpy.context.view_layer.update()
    current_height = tName.dimensions.y
    if current_height == 0:
        current_height = tElevation.dimensions.y
    if current_height == 0:
        current_height = tLength.dimensions.y
    if current_height == 0:
        current_height = 5

    scale_factor = textSize2 / current_height
    tName.scale.x *= scale_factor
    tName.scale.y *= scale_factor

    scale_factor = textSize / current_height
    tElevation.scale.x *= scale_factor
    tLength.scale.x *= scale_factor
    tDuration.scale.x *= scale_factor
    tElevation.scale.y *= scale_factor
    tLength.scale.y *= scale_factor
    tDuration.scale.y *= scale_factor

    
    convert_text_to_mesh("t_name", MapObject.name)
    convert_text_to_mesh("t_elevation", MapObject.name)
    convert_text_to_mesh("t_length", MapObject.name)
    convert_text_to_mesh("t_duration", MapObject.name)
    
    
    bpy.ops.object.select_all(action='DESELECT')

    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    #curveObj.select_set(True)
    
    bpy.context.view_layer.objects.active = tName
    
    bpy.ops.object.join()

    tName.name = name + "_Text"


    #SHAPE ROTATION
    tName.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    tName.select_set(True)
    bpy.context.view_layer.objects.active = tName
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    

    global textobj
    textobj = tName
    
def HexagonOuterText():


    
    outersize = size * ( 1 + outerBorderSize/100)
    thickness = plateThickness
    textSize = bpy.context.scene.tp3d.textSize
    textSize2 = bpy.context.scene.tp3d.textSizeTitle

    if textSize2 == 0:
        textSize2 = textSize
    
    
    verts = []
    faces = []
    for i in range(6):
        angle = math.radians(60 * i)
        x = outersize/2 * math.cos(angle)
        y = outersize/2 * math.sin(angle)
        verts.append((x, y, 0))
    verts.append((0, 0, 0))  # Center vertex
    faces = [[i, (i + 1) % 6, 6] for i in range(6)]
    mesh = bpy.data.meshes.new("HexagonOuter")
    outerHex = bpy.data.objects.new("HexagonOuter", mesh)
    bpy.context.collection.objects.link(outerHex)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    outerHex.name = name
    outerHex.data.name = name
    
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, -8))#bpy.ops.mesh.select_all(action='DESELECT')

    bpy.ops.object.mode_set(mode='OBJECT')

    # Get the mesh data
    mesh = outerHex.data

    # Get selected faces
    selected_faces = [face for face in mesh.polygons if face.select]
    
    if selected_faces:
        for face in selected_faces:
            for vert_idx in face.vertices:
                vert = mesh.vertices[vert_idx]
                vert.co.z =  - thickness;
    else:
        print("No face selected.")
    
    transform_MapObject(outerHex, centerx, centery)
    
    
    dist = (outersize - size)/4 + size/2
    
    temp_y = math.sin(math.radians(90)) * (dist  * math.cos(math.radians(30)))
    
    
    #t_name = create_text("t_name", "Name", (0, temp_y, 1 + additionalExtrusion - 2 ),text_size,(0, 0, 0),0.4)

    for i, (text_name, angle) in enumerate(zip(["t_name","t_length", "t_elevation", "t_duration"], [90 + text_angle_preset, 210 + text_angle_preset, 270 + text_angle_preset, 330 + text_angle_preset])):
        angle_centered = angle + 90
        x = math.cos(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        y = math.sin(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        rot_z = math.radians(angle_centered)
        if i == 0:
            rot_z += math.radians(180)
        create_text(text_name, text_name.split("_")[1].capitalize(), (x, y,1.4),1,  (0, 0, rot_z), 0.4)
    
    tName = bpy.data.objects.get("t_name")
    tElevation = bpy.data.objects.get("t_elevation")
    tLength = bpy.data.objects.get("t_length")
    tDuration = bpy.data.objects.get("t_duration")

    
    
    transform_MapObject(tName, centerx, centery)
    transform_MapObject(tElevation, centerx, centery)
    transform_MapObject(tLength, centerx, centery)
    transform_MapObject(tDuration, centerx, centery)
    
    
    update_text_object("t_name", f"{name}")
    update_text_object("t_elevation", f"{total_elevation:.2f} hm")
    update_text_object("t_length", f"{total_length:.2f} km")
    update_text_object("t_duration", f"{time_str}")

    if overwriteLength != "":
        update_text_object("t_length", overwriteLength)
    if overwriteHeight != "":
        update_text_object("t_elevation", overwriteHeight)
    if overwriteTime != "":
        update_text_object("t_duration", overwriteTime)

    #Scale text sizes to mm values (blender units)
    bpy.context.view_layer.update()
    current_height = tName.dimensions.y
    if current_height == 0:
        current_height = tElevation.dimensions.y
    if current_height == 0:
        current_height = tLength.dimensions.y
    if current_height == 0:
        current_height = 5
    scale_factor = textSize2 / current_height
    tName.scale.x *= scale_factor
    tName.scale.y *= scale_factor

    scale_factor = textSize / current_height
    tElevation.scale.x *= scale_factor
    tLength.scale.x *= scale_factor
    tDuration.scale.x *= scale_factor
    tElevation.scale.y *= scale_factor
    tLength.scale.y *= scale_factor
    tDuration.scale.y *= scale_factor


    
    convert_text_to_mesh("t_name", outerHex.name, False)
    convert_text_to_mesh("t_elevation", outerHex.name, False)
    convert_text_to_mesh("t_length", outerHex.name, False)
    convert_text_to_mesh("t_duration", outerHex.name, False)
    
    
    bpy.ops.object.select_all(action='DESELECT')
    
    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    
    bpy.context.view_layer.objects.active = tName

    
    bpy.ops.object.join()

    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    tName.name = name + "_Text"
    outerHex.name = name + "_Plate"

    tName.location.z += plateThickness
    outerHex.location.z += plateThickness


    #SHAPE ROTATION
    outerHex.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    outerHex.select_set(True)
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)

    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    global plateobj
    plateobj = outerHex

    global textobj
    textobj = tName


def HexagonFrontText():


    
    outersize = size * ( 1 + outerBorderSize/100)
    thickness = plateThickness
    textSize = bpy.context.scene.tp3d.textSize
    textSize2 = bpy.context.scene.tp3d.textSizeTitle

    if textSize2 == 0:
        textSize2 = textSize
    
    
    verts = []
    faces = []
    for i in range(6):
        angle = math.radians(60 * i)
        x = outersize/2 * math.cos(angle)
        y = outersize/2 * math.sin(angle)
        verts.append((x, y, 0))
    verts.append((0, 0, 0))  # Center vertex
    faces = [[i, (i + 1) % 6, 6] for i in range(6)]
    mesh = bpy.data.meshes.new("HexagonOuter")
    outerHex = bpy.data.objects.new("HexagonOuter", mesh)
    bpy.context.collection.objects.link(outerHex)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    outerHex.name = name
    outerHex.data.name = name
    
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, -8))#bpy.ops.mesh.select_all(action='DESELECT')

    bpy.ops.object.mode_set(mode='OBJECT')

    # Get the mesh data
    mesh = outerHex.data

    # Get selected faces
    selected_faces = [face for face in mesh.polygons if face.select]
    
    if selected_faces:
        for face in selected_faces:
            for vert_idx in face.vertices:
                vert = mesh.vertices[vert_idx]
                vert.co.z =  - thickness;
    else:
        print("No face selected.")
    
    transform_MapObject(outerHex, centerx, centery)
    
    dist = outersize/2
    
    temp_y = math.sin(math.radians(90)) * (dist  * math.cos(math.radians(30)))
    
    

    for i, (text_name, angle) in enumerate(zip(["t_name","t_length", "t_elevation", "t_duration"], [90 + text_angle_preset, 210 + text_angle_preset, 270 + text_angle_preset, 330 + text_angle_preset])):
        angle_centered = angle + 90
        x = math.cos(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        y = math.sin(math.radians(angle)) * (dist * math.cos(math.radians(30)))
        rot_z = math.radians(angle_centered)
        #if i == 0:
            #rot_z += math.radians(180)
        create_text(text_name, text_name.split("_")[1].capitalize(), (x, y,minThickness/2 - plateThickness / 2),1,  (math.radians(90), 0, rot_z), 0.4)
    
    tName = bpy.data.objects.get("t_name")
    tElevation = bpy.data.objects.get("t_elevation")
    tLength = bpy.data.objects.get("t_length")
    tDuration = bpy.data.objects.get("t_duration")
    
    
    transform_MapObject(tName, centerx, centery)
    transform_MapObject(tElevation, centerx, centery)
    transform_MapObject(tLength, centerx, centery)
    transform_MapObject(tDuration, centerx, centery)
    
    
    update_text_object("t_name", f"{name}")
    update_text_object("t_elevation", f"{total_elevation:.2f} hm")
    update_text_object("t_length", f"{total_length:.2f} km")
    update_text_object("t_duration", f"{time_str}")

    if overwriteLength != "":
        update_text_object("t_length", overwriteLength)
    if overwriteHeight != "":
        update_text_object("t_elevation", overwriteHeight)
    if overwriteTime != "":
        update_text_object("t_duration", overwriteTime)
    
    #Scale text sizes to mm values (blender units)
    bpy.context.view_layer.update()
    current_height = tName.dimensions.y
    if current_height == 0:
        current_height = tElevation.dimensions.y
    if current_height == 0:
        current_height = tLength.dimensions.y
    if current_height == 0:
        current_height = 5
    scale_factor = textSize2 / current_height
    tName.scale.x *= scale_factor
    tName.scale.y *= scale_factor

    scale_factor = textSize / current_height
    tElevation.scale.x *= scale_factor
    tLength.scale.x *= scale_factor
    tDuration.scale.x *= scale_factor
    tElevation.scale.y *= scale_factor
    tLength.scale.y *= scale_factor
    tDuration.scale.y *= scale_factor

    
    convert_text_to_mesh("t_name", outerHex.name, False)
    convert_text_to_mesh("t_elevation", outerHex.name, False)
    convert_text_to_mesh("t_length", outerHex.name, False)
    convert_text_to_mesh("t_duration", outerHex.name, False)
    
    
    bpy.ops.object.select_all(action='DESELECT')
    
    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    
    bpy.context.view_layer.objects.active = tName

    
    bpy.ops.object.join()
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    tName.name = name + "_Text"
    outerHex.name = name + "_Plate"

    tName.location.z += plateThickness
    outerHex.location.z += plateThickness

    #SHAPE ROTATION
    outerHex.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    outerHex.select_set(True)
    bpy.context.view_layer.objects.active = outerHex
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    global plateobj
    plateobj = outerHex

    global textobj
    textobj = tName

def OctagonOuterText():
    num_sides = 8
    outersize = size * (1 + outerBorderSize / 100)
    thickness = plateThickness
    textSize = bpy.context.scene.tp3d.textSize
    textSize2 = bpy.context.scene.tp3d.textSizeTitle

    if textSize2 == 0:
        textSize2 = textSize

    verts = []
    faces = []

    # Create vertices for octagon
    for i in range(num_sides):
        angle = math.radians(360 / num_sides * i + 22.5)
        x = outersize / 2 * math.cos(angle)
        y = outersize / 2 * math.sin(angle)
        verts.append((x, y, 0))
    verts.append((0, 0, 0))  # center vertex
    faces = [[i, (i + 1) % num_sides, num_sides] for i in range(num_sides)]

    mesh = bpy.data.meshes.new("OctagonOuter")
    outerOct = bpy.data.objects.new("OctagonOuter", mesh)
    bpy.context.collection.objects.link(outerOct)
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    outerOct.name = name
    outerOct.data.name = name

    bpy.context.view_layer.objects.active = outerOct
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, -8))
    bpy.ops.object.mode_set(mode='OBJECT')

    mesh = outerOct.data
    selected_faces = [face for face in mesh.polygons if face.select]

    if selected_faces:
        for face in selected_faces:
            for vert_idx in face.vertices:
                vert = mesh.vertices[vert_idx]
                vert.co.z = -thickness
    else:
        print("No face selected.")

    transform_MapObject(outerOct, centerx, centery)

    #Text placement
    dist = (outersize - size) / 4 + size / 2
    text_labels = ["t_name", "t_length", "t_elevation", "t_duration"]

    # Choose 4 corners of the octagon
    base_angles = [90 + text_angle_preset, 225 + text_angle_preset, 270 + text_angle_preset, 315 + text_angle_preset]

    for i, (text_name, angle) in enumerate(zip(text_labels, base_angles)):
        angle_centered = angle + 90
        x = math.cos(math.radians(angle)) * (dist * math.cos(math.radians(22.5)))
        y = math.sin(math.radians(angle)) * (dist * math.cos(math.radians(22.5)))
        rot_z = math.radians(angle_centered)
        if i == 0:
            rot_z += math.radians(180)
        print(f"text_name: {text_name}")
        create_text(text_name, text_name.split("_")[1].capitalize(), (x, y,1.4),1,  (0, 0, rot_z), 0.4)



    # Get text objects
    tName = bpy.data.objects.get("t_name")
    tElevation = bpy.data.objects.get("t_elevation")
    tLength = bpy.data.objects.get("t_length")
    tDuration = bpy.data.objects.get("t_duration")

    # Position relative to plate
    transform_MapObject(tName, centerx, centery)
    transform_MapObject(tElevation, centerx, centery)
    transform_MapObject(tLength, centerx, centery)
    transform_MapObject(tDuration, centerx, centery)

    # Set content
    update_text_object("t_name", f"{name}")
    update_text_object("t_elevation", f"{total_elevation:.2f} hm")
    update_text_object("t_length", f"{total_length:.2f} km")
    update_text_object("t_duration", f"{time_str}")

    if overwriteLength != "":
        update_text_object("t_length", overwriteLength)
    if overwriteHeight != "":
        update_text_object("t_elevation", overwriteHeight)
    if overwriteTime != "":
        update_text_object("t_duration", overwriteTime)
    
    #Scale text sizes to mm values (blender units)
    bpy.context.view_layer.update()
    current_height = tName.dimensions.y
    if current_height == 0:
        current_height = tElevation.dimensions.y
    if current_height == 0:
        current_height = tLength.dimensions.y
    if current_height == 0:
        current_height = 5
    scale_factor = textSize2 / current_height
    tName.scale.x *= scale_factor
    tName.scale.y *= scale_factor

    scale_factor = textSize / current_height
    tElevation.scale.x *= scale_factor
    tLength.scale.x *= scale_factor
    tDuration.scale.x *= scale_factor
    tElevation.scale.y *= scale_factor
    tLength.scale.y *= scale_factor
    tDuration.scale.y *= scale_factor

    # Convert to mesh
    convert_text_to_mesh("t_name", outerOct.name, False)
    convert_text_to_mesh("t_elevation", outerOct.name, False)
    convert_text_to_mesh("t_length", outerOct.name, False)
    convert_text_to_mesh("t_duration", outerOct.name, False)

    # Join text objects
    bpy.ops.object.select_all(action='DESELECT')
    tName.select_set(True)
    tElevation.select_set(True)
    tLength.select_set(True)
    tDuration.select_set(True)
    bpy.context.view_layer.objects.active = tName
    bpy.ops.object.join()
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    tName.name = name + "_Text"
    outerOct.name = name + "_Plate"

    tName.location.z += plateThickness
    outerOct.location.z += plateThickness


    #SHAPE ROTATION
    outerOct.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    outerOct.select_set(True)
    bpy.context.view_layer.objects.active = outerOct
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')

    global plateobj
    plateobj = outerOct

    global textobj
    textobj = tName
    
def BottomText(obj):
    
    global total_elevation
    global total_length


    name = obj.name
    if "objSize" in obj:
        size = obj["objSize"]
    else:
        return
    
    thickness = 0.1
        # Place text objects
    text_size = (size / 10)
    
    
    dist =  (size/2 - size/2 * (1-pathScale)/2)
    
    temp_y = size/4
    temp_y = 0
    
    
    global additionalExtrusion
    additionalExtrusion = obj["AdditionalExtrusion"]
    
    tName = create_text("t_name", "Name", (0, 0,1.1),text_size)
    

    cx = obj.location.x
    cy = obj.location.y
    
    transform_MapObject(tName, cx, cy)
    
    tName.data.extrude = 0.1
    
    tName.scale.x *= -1

    
    update_text_object("t_name", name)
    
    convert_text_to_mesh("t_name", obj.name, False)
    
    tName.name = name + "_Mark"
    
    bpy.ops.object.select_all(action='DESELECT')

    tName.select_set(True)
    
    bpy.context.view_layer.objects.active = tName

    mat = bpy.data.materials.get("TRAIL")
    tName.data.materials.clear()
    tName.data.materials.append(mat)
    

def convert_text_to_mesh(text_obj_name, mesh_obj_name, merge = True):
    # Get the text and mesh objects
    text_obj = bpy.data.objects.get(text_obj_name)
    mesh_obj = bpy.data.objects.get(mesh_obj_name)
    
    if not text_obj or not mesh_obj:
        print("One or both objects not found")
        return
    
    # Ensure the text object is selected and active
    bpy.ops.object.select_all(action='DESELECT')
    text_obj.select_set(True)
    bpy.context.view_layer.objects.active = text_obj
    
    # Convert text to mesh
    bpy.ops.object.convert(target='MESH')
    
    # Enter edit mode
    bpy.ops.object.mode_set(mode='EDIT')
    
    # Enable auto-merge vertices
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.remove_doubles(threshold=0.002)
    #bpy.context.tool_settings.use_mesh_automerge = True
    
    # Switch back to object mode to move it
    bpy.ops.object.mode_set(mode='OBJECT')

    recalculateNormals(text_obj)
    
    # Move the text object up by 1
    text_obj.location.z += 1
    
    # Move the text object down by 1 (merging overlapping vertices)
    text_obj.location.z -= 1
    
    # Disable auto-merge vertices
    bpy.context.tool_settings.use_mesh_automerge = False
    
    if merge == True:
        # Add boolean modifier
        bool_mod = text_obj.modifiers.new(name="Boolean", type='BOOLEAN')
        bool_mod.object = mesh_obj
        bool_mod.operation = 'INTERSECT'
        bool_mod.solver = 'MANIFOLD'

        
        # Apply the boolean modifier
        bpy.ops.object.select_all(action='DESELECT')
        text_obj.select_set(True)
        bpy.context.view_layer.objects.active = text_obj
        bpy.ops.object.modifier_apply(modifier=bool_mod.name)
    
        # Move the text object up by 1
        text_obj.location.z += 0.4

def intersect_trails_with_existing_box(cutobject):
    #cutobject is the object that will be cut to the Map shapes
    cutobject.scale.z = 1000

    
    
    bpy.context.view_layer.objects.active = cutobject
    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
    
    #cube = bpy.data.objects.get(cutobject)
    cube = cutobject
    if not cube:
        print(f"Object named '{cutobject}' not found.")
        return

    # Get cube's bounding box in world coordinates
    cube_bb = [cube.matrix_world @ Vector(corner) for corner in cube.bound_box]


    def is_point_inside_cube(point, bb):
        min_corner = Vector((min(v[0] for v in bb),
                             min(v[1] for v in bb),
                             min(v[2] for v in bb)))
        max_corner = Vector((max(v[0] for v in bb),
                             max(v[1] for v in bb),
                             max(v[2] for v in bb)))
        return all(min_corner[i] <= point[i] <= max_corner[i] for i in range(3))
    done = False
    boolObjects = []
    for robj in bpy.data.objects:
        if "_Trail" in robj.name and robj.type in {'CURVE', 'MESH'}:
            if not robj.hide_get():
                # Convert curve to mesh
                if robj.type == 'CURVE':
                    bpy.context.view_layer.objects.active = robj
                    bpy.ops.object.select_all(action='DESELECT')
                    robj.select_set(True)
                    bpy.ops.object.convert(target='MESH')
                    trail_mesh = robj
                else:
                    trail_mesh = robj
                
                #robj.hide_set(True)

                if trail_mesh:
                    if trail_mesh.type == "MESH" and len(trail_mesh.data.vertices) > 0:
                        # Check if any vertex is inside the cube
                        for v in trail_mesh.data.vertices:
                            global_coord = trail_mesh.matrix_world @ v.co
                            if is_point_inside_cube(global_coord, cube_bb):
                                # Apply Boolean modifier
                                #print(f"{trail_mesh.name} is inside the Boundaries")
                                if trail_mesh not in boolObjects:
                                    boolObjects.append(trail_mesh)
                                #Set done to True so it doesnt delete the object later
                                done = True
                                #Change Collection
                                continue  # No need to keep checking this object
                            else:
                                pass
                                #print(f"{trail_mesh.name} is NOT inside the Boundaries")
                    else:
                        print("No Vertices for Trail Found")
                        bpy.data.objects.remove(trail_mesh, do_unlink=True)
                
                #bpy.data.objects.remove(robj, do_unlink=True)
                #break
    if done == False:
        #print("No matching trail found. removing cutobject")
        bpy.data.objects.remove(cutobject, do_unlink=True)
    #Pfade kopieren, zusammenfügen und die boolean operation mit allen trails kombiniert ausführen
    if done == True:
        copied_objects = []
        #Copy objects
        for obj in boolObjects:
            print(f"Copy obj {obj.name}")
            obj_copy = obj.copy()
            obj_copy.data = obj.data.copy()
            bpy.context.collection.objects.link(obj_copy)
            copied_objects.append(obj_copy)
        
        #Deselect all
        bpy.ops.object.select_all(action='DESELECT')

        #Select all copied objects and make one active
        for obj in copied_objects:
            obj.select_set(True)
        bpy.context.view_layer.objects.active = copied_objects[0]

        #Join them into a single object
        bpy.ops.object.join()

        merged_object = bpy.context.active_object

        bool_mod = cube.modifiers.new(name=f"Intersect", type='BOOLEAN')
        bool_mod.operation = 'INTERSECT'
        bool_mod.object = merged_object
        bpy.context.view_layer.objects.active = cube
        bpy.ops.object.modifier_apply(modifier=bool_mod.name)

        bpy.data.objects.remove(merged_object, do_unlink=True)

        writeMetadata(cube,"TRAIL")


def separate_duplicate_xy(coordinates, offset=0.05):
    seen_xy = set()

    for i, point in enumerate(coordinates):
        # Convert tuple to list if needed
        if isinstance(point, tuple):
            point = list(point)
            coordinates[i] = point  # Update the original array with the list version

        x, y, z = point[0], point[1], point[2]
        xy_key = (x, y,z)

        if xy_key in seen_xy:
            point[2] += offset
            point[1] += offset
            #print("Duplicate")
        else:
            seen_xy.add(xy_key)
    
    return(coordinates)

def single_color_mode(crv, mapName):
    """
    单色模式处理：将路径嵌入到地图中，适合单色3D打印机
    
    工作原理：
    1. 将路径曲线转换为网格并与地图相交
    2. 创建稍厚的路径副本
    3. 使用布尔操作从地图中减去厚路径，创建凹槽
    4. 将原始路径放入凹槽中，使其与地图平齐
    
    注意：此函数必须在plateInsert之后调用，以避免底板包含路径信息
    
    参数：
        crv: 路径曲线对象
        mapName: 地图对象的名称
    """
    map = bpy.data.objects.get(mapName)
    tol = bpy.context.scene.tp3d.tolerance
    print(f"单色模式容差: {tol}")
    crv_data = crv.data
    crv_data.dimensions = "2D"
    crv_data.dimensions = "3D"
    crv_data.extrude = 200

    # Ensure the text object is selected and active
    bpy.ops.object.select_all(action='DESELECT')
    crv.select_set(True)
    bpy.context.view_layer.objects.active = crv

    bpy.ops.object.mode_set(mode='EDIT')

    # select all points if you want to smooth everything
    bpy.ops.curve.select_all(action='SELECT')

    # run the smooth operator   
    bpy.ops.curve.smooth()

    # back to Object Mode if you like
    bpy.ops.object.mode_set(mode='OBJECT')

    #Create a duplicate object of the curve that will be slightly thicker
    crv_thick = crv.copy()
    crv_thick.data = crv.data.copy()
    crv_thick.data.bevel_depth = pathThickness/2 + tol  # Set the thickness of the curve
    bpy.context.collection.objects.link(crv_thick)



    bpy.ops.object.convert(target='MESH')

    recalculateNormals(crv)

    # Add boolean modifier
    bool_mod = crv.modifiers.new(name="Boolean", type='BOOLEAN')
    bool_mod.object = map
    bool_mod.operation = 'INTERSECT'
    bool_mod.solver = 'MANIFOLD'


    bpy.ops.object.modifier_apply(modifier=bool_mod.name)

    for v in crv.data.vertices:
        v.co += Vector((0,0,1))

    recalculateNormals(crv)

    #Adding another Intersect Modifier to make the path "Plane" with the Map
    # Add boolean modifier
    bool_mod = crv.modifiers.new(name="Boolean", type='BOOLEAN')
    bool_mod.object = map
    bool_mod.operation = 'INTERSECT'
    bool_mod.solver = 'MANIFOLD'

    recalculateNormals(crv)

    bpy.ops.object.modifier_apply(modifier=bool_mod.name)

    #doing the same for the duplicate
    bpy.ops.object.select_all(action='DESELECT')
    crv_thick.select_set(True)
    bpy.context.view_layer.objects.active = crv_thick
    bpy.ops.object.convert(target='MESH')


    # Add boolean modifier
    bool_mod = crv_thick.modifiers.new(name="Boolean", type='BOOLEAN')
    bool_mod.object = map
    bool_mod.operation = 'INTERSECT'
    bool_mod.solver = 'MANIFOLD'

    bpy.ops.object.modifier_apply(modifier=bool_mod.name)

    # Move the text object up by x
    crv_thick.location.z += 1

    bpy.ops.object.select_all(action='DESELECT')
    map.select_set(True)
    bpy.context.view_layer.objects.active = map

    bool_mod = map.modifiers.new(name="Boolean", type="BOOLEAN")
    bool_mod.object = crv_thick
    bool_mod.operation = "DIFFERENCE"
    bool_mod.solver = "MANIFOLD"


    bpy.ops.object.modifier_apply(modifier = bool_mod.name)
    bpy.data.objects.remove(crv_thick, do_unlink = True)

    #NORMALS FLIPPEN
    """
    Werden vor dem Skript geflippt
    bpy.ops.object.select_all(action='DESELECT')
    map.select_set(True)
    bpy.context.view_layer.objects.active = map
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_mode(type="FACE")
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.normals_make_consistent(inside=False)
    bpy.ops.object.mode_set(mode='OBJECT')
    """


# --- OSM FETCHING ---

def fetch_osm_data(bbox, kind = "WATER"):
    south, west, north, east = bbox
    overpass_url = "http://overpass-api.de/api/interpreter"
    if kind == "WATER":
        query = f"""
        [out:json][timeout:25];
        (
            nwr["natural"="water"]({south},{west},{north},{east});
            nwr["water"="river"]({south},{west},{north},{east});
            nwr["water"="lake"]({south},{west},{north},{east});

        );
        out body;
        >;
        out skel qt;
        """
    if kind == "FOREST":
        query = f"""
        [out:json][timeout:25];
        (
            nwr["natural"="wood"]({south},{west},{north},{east});
            nwr["landuse"="forest"]({south},{west},{north},{east});

        );
        out body;
        >;
        out skel qt;
        """
    if kind == "CITY":
        query = f"""
        [out:json][timeout:25];
        (
            nwr["landuse"~"residential|urban|commercial|industrial"]({south},{west},{north},{east});


        );
        out body;
        >;
        out skel qt;
        """

    '''
    #way["landuse"~"residential|urban|commercial|industrial"]({south},{west},{north},{east});
    #relation["landuse"~"residential|urban|commercial|industrial"]({south},{west},{north},{east});

    nwr["natural"="water"]({south},{west},{north},{east});
    nwr["water"="river"]({south},{west},{north},{east});
    nwr["water"="lake"]({south},{west},{north},{east});
    

        way["natural"="water"]({south},{west},{north},{east});
        relation["natural"="water"]({south},{west},{north},{east});

        way["water"="river"]({south},{west},{north},{east});
        relation["water"="river"]({south},{west},{north},{east});

        way["waterway"="river"]({south},{west},{north},{east});
        way["waterway"="stream"]({south},{west},{north},{east});

    '''
    #print(query)
    for attempt in range(3):
        try:
            response = requests.post(overpass_url, data={'data': query})

            #check if response is valid
            print("Status:", response.status_code)
            if response.status_code != 200:
                print("Content-Type:", response.headers.get("content-type"))
                print("Response text preview:\n", response.text[:500])

            #print(response.json())
            if response.status_code == 504:
                print(f"Timeout (504), retrying... {attempt+1}/3")
            if response.status_code == 200:
                return response
            
        except Exception as e:
            print("Request failed:", e)
            time.sleep(5)

    return None


def extract_multipolygon_bodies(elements, nodes):

    # Helper to get coordinates of a way by its node ids
    def way_coords(way):
        return [ (nodes[nid]['lat'], nodes[nid]['lon'], nodes[nid].get('elevation', 0)) for nid in way['nodes'] if nid in nodes ]

    # Store all multipolygon lakes as lists of outer rings (each ring = list of coords)
    multipolygon_lakes = []

    # Index ways by their id for quick lookup
    way_dict = {el['id']: el for el in elements if el['type'] == 'way'}

    for el in elements:
        if el['type'] in ('relation', 'way'):
            # Collect outer and inner member ways
            outer_ways = []
            inner_ways = []

            for member in el.get('members', []):
                if member['type'] != 'way':
                    continue
                way = way_dict.get(member['ref'])
                if not way:
                    continue

                role = member.get('role', '')
                if role == 'outer':
                    outer_ways.append(way)
                elif role == 'inner':
                    inner_ways.append(way)

            # Stitch ways to closed loops for outer and inner rings
            def stitch_ways(ways):
                loops = []
                # Convert ways to list of coords
                ways_coords = [way_coords(w) for w in ways]

                while ways_coords:
                    current = ways_coords.pop(0)
                    changed = True
                    while changed:
                        changed = False
                        i = 0
                        while i < len(ways_coords):
                            w = ways_coords[i]

                            # Check if current end connects to w start or end
                            if w:
                                if current[-1] == w[0]:
                                    current.extend(w[1:])
                                    ways_coords.pop(i)
                                    changed = True
                                elif current[-1] == w[-1]:
                                    current.extend(reversed(w[:-1]))
                                    ways_coords.pop(i)
                                    changed = True
                                # Also check if current start connects to w end or start
                                elif current[0] == w[-1]:
                                    current = w[:-1] + current
                                    ways_coords.pop(i)
                                    changed = True
                                elif current[0] == w[0]:
                                    current = list(reversed(w[1:])) + current
                                    ways_coords.pop(i)
                                    changed = True
                                else:
                                    i += 1
                    loops.append(current)

                return loops

            outer_loops = stitch_ways(outer_ways)
            inner_loops = stitch_ways(inner_ways)

            # For now, just add outer loops as separate lakes (you could add inner loops for holes)
            for loop in outer_loops:
                multipolygon_lakes.append(loop)

    return multipolygon_lakes



# --- COLOR MESH CREATION ---

def col_create_line_mesh(name, coords):
    mesh = bpy.data.meshes.new(name)
    tobj = bpy.data.objects.new(name, mesh)
    bpy.context.collection.objects.link(tobj)

    bm = bmesh.new()
    verts = [bm.verts.new(c) for c in coords]
    for i in range(len(verts) - 1):
        bm.edges.new((verts[i], verts[i + 1]))
    bm.to_mesh(mesh)
    bm.free()
    return tobj


def col_create_face_mesh(name, coords):

    if len(coords) < 3:
        return  # Need at least 3 points for a face
    

    mesh = bpy.data.meshes.new(name)
    tobj = bpy.data.objects.new(name, mesh)
    bpy.context.collection.objects.link(tobj)

    bm = bmesh.new()
    verts = [bm.verts.new(c) for c in coords]
    try:
        bm.faces.new(verts)
        pass
    except ValueError:
        print(ValueError)
        pass  # face might already exist or be invalid
    bm.to_mesh(mesh)
    bm.free()
    return tobj

def calculate_polygon_area_2d(coords):
    area = 0.0
    
    if len(coords) >= 3:
    
        n = len(coords)
        for i in range(n):
            x0, y0, z0 = coords[i]
            x1, y1, z1 = coords[(i + 1) % n]  # Wrap around to the first point
            area += (x0 * y1) - (x1 * y0)
    
    return abs(area) * 0.5

def build_osm_nodes(data):
    nodes = {}
    for element in data['elements']:
        if element['type'] == 'node':
            nodes[element['id']] = element
    return nodes



def coloring_main(map,kind = "WATER"):

    col_KeepManifold = (bpy.context.scene.tp3d.col_KeepManifold)
    if kind == "WATER":
        col_Area = (bpy.context.scene.tp3d.col_wArea)
    if kind == "FOREST":
        col_Area = (bpy.context.scene.tp3d.col_fArea)
    if kind == "CITY":
        col_Area = (bpy.context.scene.tp3d.col_cArea)
    
    col_PaintMap = (bpy.context.scene.tp3d.col_PaintMap)



    bpy.context.preferences.edit.use_global_undo = False

    #print(f"ADDING {kind} MESH")
    #print(f"Map name: {map.name}")

    name = map.name

    lat_step = 2
    lon_step = 2

    waterDeleted = 0
    waterCreated = 0

    if maxLat - minLat < lat_step:
        lat_step = maxLat - minLat
    if maxLon - minLon < lon_step:
        lon_step = maxLon - minLon

    lats = math.ceil((maxLat - minLat) / lat_step)
    lons = math.ceil((maxLon - minLon) / lon_step)

    created_objects = []

    #print(f"lats: {lats}, lons: {lons}")
    if lats * lons < 20:
        for k in range(lats):
            for l in range(lons):
                print(f"loop: {((k) * lons + l + 1)}/{lats * lons}")
                south = minLat + k * lat_step
                north = south + lat_step
                west = minLon + l * lon_step
                east = west + lon_step

                bbox = (south, west, north, east)
                data = []
                #data = fetch_osm_data(bbox, kind)
                try:
                    #pass
                    resp = fetch_osm_data(bbox, kind)
                    if resp.status_code != 200:
                        print("OSM Timeout")
                        return
                    

                except:
                    show_message_box("获取OSM数据时出错，请重试")
                    continue

                data = resp.json()
                nodes = build_osm_nodes(data)
                bodies = extract_multipolygon_bodies(data['elements'], nodes)
                #print(f"Nodes: {len(nodes)}, Bodies: {len(bodies)}")

                for i, coords in enumerate(bodies):
                    blender_coords = [convert_to_blender_coordinates(lat, lon, ele, 0) for lat, lon, ele in coords]
                    calcArea = calculate_polygon_area_2d(blender_coords)
                    #print(f"tArea1: {calcArea}")
                    if calcArea > col_Area:
                        tobj = col_create_face_mesh(f"LakeRelation_{i}", blender_coords)
                        created_objects.append(tobj)
                        waterCreated += 1
                    else:
                        waterDeleted += 1

                for i, element in enumerate(data['elements']):
                    #print(i)
                    if element['type'] != 'way':
                        waterDeleted += 1
                        continue

                    coords = []
                    for node_id in element.get('nodes', []):
                        if node_id in nodes:
                            node = nodes[node_id]
                            coord = convert_to_blender_coordinates(
                                node['lat'], node['lon'], 0,0
                            )
                            coords.append(coord)
                    tArea = calculate_polygon_area_2d(coords)
                    #print(f"tArea2: {tArea}")
                    if len(coords) < 2 or tArea < col_Area:
                        waterDeleted += 1
                        continue
                    
                    tags = element.get("tags", {})
                    if tags.get("natural") == "water" or tags.get("natural") == "peak" or 1 == 1:
                        if coords[0] == coords[-1]:
                            tobj = col_create_face_mesh(f"Lake_{i}", coords)
                            created_objects.append(tobj)
                            waterCreated += 1
                        else:
                            tobj = col_create_line_mesh(f"OpenWater_{i}", coords)
                            created_objects.append(tobj)
                            waterCreated += 1
                    elif "waterway" in tags:
                        pass
                        waterDeleted += 1
                        #create_line_mesh(f"Waterway_{i}", coords)
                    
                time.sleep(5)  # Pause to prevent request throttling
    else:
        print("Region too big. Cant Fetch All Water Sources")
            
    # --- Merge all created water meshes into one ---

    print(f"{kind} Objects Created: {waterCreated}, Objects Ignored: {waterDeleted}")

    #print(f"Creating {kind} Objects")
    if created_objects:
        ctx = bpy.context
        bpy.ops.object.select_all(action='DESELECT')
        found = 0
        biggestArea = 0
        for tobj in created_objects:
            
            bm = bmesh.new()
            bm.from_mesh(tobj.data)
            area = sum(f.calc_area() for f in bm.faces)
            bm.free()
            #print(f"Area: {area}")
            if area > biggestArea:
                biggestArea = area
            if area >= col_Area:
                found = 1
                tobj.select_set(True)
                ctx.view_layer.objects.active = tobj
                #print(f"Area: {area}")
            else:
                mesh_data = tobj.data
                bpy.data.objects.remove(tobj, do_unlink=True)
                bpy.data.meshes.remove(mesh_data)
                #print("Removed")

            if found == 0:
                continue
        
        print(f"Biggest {kind} Found has a Area of: {biggestArea}")

        if biggestArea == 0:
            print("No Water Found on Tile")
            return
        
        bpy.ops.object.join()  # This merges them into the active object
        
        merged_object = ctx.view_layer.objects.active
        bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')


        #SETUP FOR MODIFIERS
        
        bpy.context.view_layer.objects.active = merged_object
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.mesh.select_all(action='SELECT')
        bpy.ops.mesh.extrude_region_move()
        bpy.ops.transform.translate(value=(0, 0, 200))#bpy.ops.mesh.select_all(action='DESELECT')
        bpy.ops.object.mode_set(mode='OBJECT')
        merged_object.location.z -= 1


        #Add Decimate modifier
        #dec_mod = merged_object.modifiers.new(name="Decimate", type="DECIMATE")
        #dec_mod.decimate_type = "UNSUBDIV"
        #dec_mod.iterations = 1

        #bpy.ops.object.modifier_apply(modifier=dec_mod.name)

        recalculateNormals(merged_object)


        # Add boolean modifier
        bool_mod = merged_object.modifiers.new(name="Boolean", type='BOOLEAN')
        bool_mod.object = map
        bool_mod.operation = 'INTERSECT'
        bool_mod.solver = 'MANIFOLD'


        #appla boolean modifier
        bpy.ops.object.modifier_apply(modifier=bool_mod.name)


        bpy.ops.object.mode_set(mode="EDIT")
        bm = bmesh.from_edit_mesh(merged_object.data)

        bm.verts.ensure_lookup_table()
        bm.faces.ensure_lookup_table()


        #Get lowest Vertice
        try:
            min_z = min(v.co.z for v in bm.verts)
        #IF NO VERTICES ARE LEFT, END FUNCTION
        except:
            bpy.ops.object.mode_set(mode='OBJECT')
            return
        
        tol = 0.1

        lowestVert = 100
        for v in bm.verts:
            if abs(v.co.z - min_z) < tol:
                v.select = True
            else:
                v.select = False
                if v.co.z < lowestVert:
                    lowestVert = v.co.z
        
        bpy.context.tool_settings.mesh_select_mode = (True, False, False)
        bmesh.ops.delete(bm, geom=[elem for elem in bm.verts[:] + bm.edges[:] + bm.faces[:] if elem.select], context='VERTS')
    

        bpy.ops.mesh.select_all(action='SELECT')
        bpy.ops.mesh.extrude_region_move()
        bpy.ops.transform.translate(value=(0, 0, -1))#bpy.ops.mesh.select_all(action='DESELECT')


        bmesh.update_edit_mesh(merged_object.data)
        bpy.ops.object.mode_set(mode="OBJECT")

        #recalculate normals again after the Boolean operation
        recalculateNormals(merged_object)

        #Disabled for now
        if col_KeepManifold == 0 and 1 == 0:
            delete_non_manifold(merged_object)

        #merged_object.location.z += 0.05
        merged_object.name = name + "_" + kind

        bpy.context.view_layer.objects.active = merged_object
        merged_object.select_set(True)


        meshm = merged_object.data
        for i, vert in enumerate(meshm.vertices):
            vert.co.z -= 0.9
        merged_object.location.z = 0

        #bpy.ops.object.transform_apply(location=True, rotation=False, scale=False)
        

        if merged_object:
            #print(f"Merged obj: {merged_object}, Kind: {kind}")
            writeMetadata(merged_object,kind)
            mat = bpy.data.materials.get(kind)
            merged_object.data.materials.clear()
            merged_object.data.materials.append(mat)
        
        if col_PaintMap == False:
            export_to_STL(merged_object)

        if col_PaintMap == True:
            color_map_faces_by_terrain(map, merged_object)
            mesh_data = merged_object.data
            bpy.data.objects.remove(merged_object, do_unlink=True)
            bpy.data.meshes.remove(mesh_data)

    for area in bpy.context.screen.areas:
        if area.type == 'VIEW_3D':  # make sure it's a 3D Viewport
            for space in area.spaces:
                if space.type == 'VIEW_3D':
                    space.shading.type = 'MATERIAL'  # switch shading

                
    bpy.context.preferences.edit.use_global_undo = True

def color_map_faces_by_terrain(map_obj, terrain_obj, up_threshold=0.5):
    """
    Loops through every face of map_obj.
    If face is facing upwards, raycasts upwards to see if terrain_obj is above.
    If yes, colors the face with terrain_obj's material.
    
    up_threshold = dot(normal, Z) must be greater than this (0.5 ~ 60° angle limit).
    """
    if map_obj.type != 'MESH' or terrain_obj.type != 'MESH':
        print("Both inputs must be mesh objects.")
        return

    # Ensure both have mesh data
    map_mesh = map_obj.data
    terrain_mesh = terrain_obj.data

    # Build bmesh for Map
    bm = bmesh.new()
    bm.from_mesh(map_mesh)
    bm.faces.ensure_lookup_table()

    # Build BVH tree for Terrain
    verts = [v.co for v in terrain_mesh.vertices]
    polys = [p.vertices for p in terrain_mesh.polygons]
    bvh = bvhtree.BVHTree.FromPolygons(verts, polys)

    # Get or create a material for terrain color
    if terrain_obj.active_material:
        mat = terrain_obj.active_material
    else:
        mat = bpy.data.materials.new(name="TerrainColor")
        terrain_obj.data.materials.append(mat)

    # Make sure Map has material slots
    if mat.name not in [m.name for m in map_mesh.materials]:
        map_mesh.materials.append(mat)
    mat_index = map_mesh.materials.find(mat.name)

    up = Vector((0, 0, 1))
    colored_count = 0

    for f in bm.faces:
        normal = f.normal.normalized()
        dot = normal.dot(up)

        # Only consider faces facing upward
        if dot > up_threshold:
            center = f.calc_center_median()
            loc, norm, idx, dist = bvh.ray_cast(center, up)

            if loc is not None and dist > 0:
                # Assign terrain material to this face
                f.material_index = mat_index
                colored_count += 1

    bm.to_mesh(map_mesh)
    bm.free()

    print(f"Colored {colored_count} faces on {map_obj.name} based on {terrain_obj.name}")
    

       
def merge_with_map(mapobject, mergeobject):



    print(mapobject.name)
    print(mergeobject.name)
    print(mergeobject.type)

    bpy.ops.object.select_all(action="DESELECT")

    #if the mergeobject is a Text object -> Convert it into a mesh
    if mergeobject.type == "FONT":
        mergeobject.select_set(True)
        bpy.context.view_layer.objects.active = mergeobject
        bpy.ops.object.convert(target='MESH')

    if mergeobject.type == "CURVE":
        mergeobject.select_set(True)
        bpy.context.view_layer.objects.active = mergeobject
        bpy.ops.object.convert(target='MESH')


    bpy.context.view_layer.objects.active = mergeobject
    mergeobject.select_set(True)
    bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, 200))#bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.object.mode_set(mode='OBJECT')
    mergeobject.location.z = -1

    recalculateNormals(mergeobject)



    # Add boolean modifier
    bool_mod = mergeobject.modifiers.new(name="Boolean", type='BOOLEAN')
    bool_mod.object = mapobject
    bool_mod.operation = 'INTERSECT'
    bool_mod.solver = 'MANIFOLD'

    #apply boolean modifier
    bpy.ops.object.modifier_apply(modifier=bool_mod.name)

    bpy.ops.object.mode_set(mode="EDIT")
    bm = bmesh.from_edit_mesh(mergeobject.data)

    bm.verts.ensure_lookup_table()
    bm.faces.ensure_lookup_table()



    try:
        min_z = min(v.co.z for v in bm.verts)
    except:
        bpy.ops.object.mode_set(mode='OBJECT')
        return
    
    tol = 0.1
    print(min_z)

    lowestVert = 100


    
    for v in bm.verts:
        if abs(v.co.z - min_z) < tol:
            v.select = True
        else:
            v.select = False
            if v.co.z < lowestVert:
                lowestVert = v.co.z
    
    print(lowestVert)

    
    bpy.context.tool_settings.mesh_select_mode = (True, False, False)
    #bmesh.ops.delete(bm, geom=[f for f in bm.faces if f.select], context="FACES")
    #bmesh.ops.delete(bm, geom=[v for v in bm.verts if not v.link_faces], context='VERTS')
    bmesh.ops.delete(bm, geom=[elem for elem in bm.verts[:] + bm.edges[:] + bm.faces[:] if elem.select], context='VERTS')

    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.transform.translate(value=(0, 0, -1))#bpy.ops.mesh.select_all(action='DESELECT')




    bmesh.update_edit_mesh(mergeobject.data)
    bpy.ops.object.mode_set(mode="OBJECT")

    mergeobject.location.z += 0.05
    
def midpoint_spherical(lat1, lon1, lat2, lon2):
    # Convert degrees to radians
    lat1_rad = math.radians(lat1)
    lon1_rad = math.radians(lon1)
    lat2_rad = math.radians(lat2)
    lon2_rad = math.radians(lon2)

    # Convert to Cartesian coordinates
    x1 = math.cos(lat1_rad) * math.cos(lon1_rad)
    y1 = math.cos(lat1_rad) * math.sin(lon1_rad)
    z1 = math.sin(lat1_rad)

    x2 = math.cos(lat2_rad) * math.cos(lon2_rad)
    y2 = math.cos(lat2_rad) * math.sin(lon2_rad)
    z2 = math.sin(lat2_rad)

    # Average the vectors
    x = (x1 + x2) / 2
    y = (y1 + y2) / 2
    z = (z1 + z2) / 2

    # Convert back to spherical coordinates
    lon_mid = math.atan2(y, x)
    hyp = math.sqrt(x * x + y * y)
    lat_mid = math.atan2(z, hyp)

    # Convert radians back to degrees
    return math.degrees(lat_mid), math.degrees(lon_mid)

def move_coordinates(lat, lon, distance_km, direction):
    """
    Move a point a given distance (in km) in a cardinal direction (N, S, E, W).
    """
    R = 6371.0  # Earth radius in km
    direction = direction.lower()
    
    # Convert latitude and longitude from degrees to radians
    lat_rad = math.radians(lat)
    lon_rad = math.radians(lon)

    if direction == "n":
        lat_rad += distance_km / R
    elif direction == "s":
        lat_rad -= distance_km / R
    elif direction == "e":
        lon_rad += distance_km / (R * math.cos(lat_rad))
    elif direction == "w":
        lon_rad -= distance_km / (R * math.cos(lat_rad))
    else:
        raise ValueError("Direction must be 'n', 's', 'e', or 'w'")
    
    # Convert radians back to degrees
    new_lat = math.degrees(lat_rad)
    new_lon = math.degrees(lon_rad)

    return new_lat, new_lon

def delete_non_manifold(object):

    bpy.ops.object.select_all(action="DESELECT")

    #if the mergeobject is a Text object -> Convert it into a mesh
    object.select_set(True)
    bpy.context.view_layer.objects.active = object

    # Make sure you're in edit mode
    bpy.ops.object.mode_set(mode='EDIT')

    # Get the active mesh
    obj = bpy.context.edit_object
    me = obj.data

    # Access the BMesh representation
    bm = bmesh.from_edit_mesh(me)

    # Ensure the mesh has up-to-date normals and edges
    bm.normal_update()

    # Deselect everything first (optional)
    bpy.ops.mesh.select_all(action='DESELECT')

    # Select non-manifold edges
    bpy.ops.mesh.select_non_manifold()

    # (Optional) Update the mesh to reflect selection in UI
    bmesh.update_edit_mesh(me, loop_triangles=True)

    bpy.ops.mesh.delete(type='VERT')

    bpy.ops.object.mode_set(mode='OBJECT')

def plateInsert(plate,map):
    """
    底座下凹处理：在底板上创建与地图形状匹配的凹槽
    
    工作原理：
    1. 复制地图对象并稍微放大（加上容差）
    2. 将底板上移指定距离
    3. 使用布尔差集操作从底板中减去放大的地图副本
    4. 这样地图可以嵌入到底板的凹槽中
    
    重要：此函数必须在single_color_mode之前调用
           否则底板会包含已合并的路径信息
    
    参数：
        plate: 底板对象
        map: 地图对象（应该是未合并路径的原始地图）
    """
    tol = bpy.context.scene.tp3d.tolerance
    dist = bpy.context.scene.tp3d.plateInsertValue

    # 复制地图对象并稍微放大以创建合适的间隙
    map_copy = map.copy()
    map_copy.data = map.data.copy()
    bpy.context.collection.objects.link(map_copy)
    map_copy.scale *= (size + tol) / size

    plate.location.z += dist

    bpy.ops.object.select_all(action="DESELECT")
    plate.select_set(True)
    bpy.context.view_layer.objects.active = plate

    # 使用布尔操作从底板中减去地图形状
    mod = plate.modifiers.new(name="Boolean", type='BOOLEAN')
    mod.operation = 'DIFFERENCE'
    mod.solver = "MANIFOLD"
    mod.object = map_copy

    bpy.ops.object.modifier_apply(modifier = mod.name)
    
    bpy.ops.object.origin_set(type='ORIGIN_CURSOR')

    # 删除临时的地图副本
    bpy.data.objects.remove(map_copy, do_unlink=True)

def selectBottomFaces(obj):

    if obj is None or obj.type != 'MESH':
        raise Exception("Please select a mesh object.")


    # Enter Edit Mode
    bpy.ops.object.mode_set(mode='EDIT')
    mesh = bmesh.from_edit_mesh(obj.data)

    # Recalculate normals
    bmesh.ops.recalc_face_normals(mesh, faces=mesh.faces)

    # Threshold for downward-facing
    threshold = -0.99

    # Object world matrix for local-to-global transformation
    world_matrix = obj.matrix_world


    for f in mesh.faces:
        if f.normal.normalized().z < threshold:
            f.select = True  # Optional: visually select in viewport
        else:
            f.select = False

    # Update the mesh
    bmesh.update_edit_mesh(obj.data, loop_triangles=False)

def selectTopFaces(obj):
    if obj is None or obj.type != 'MESH':
        raise Exception("Please select a mesh object.")


    # Enter Edit Mode
    bpy.ops.object.mode_set(mode='EDIT')
    mesh = bmesh.from_edit_mesh(obj.data)

    # Recalculate normals
    bmesh.ops.recalc_face_normals(mesh, faces=mesh.faces)

    # Threshold for downward-facing
    threshold = 0.99

    # Object world matrix for local-to-global transformation
    world_matrix = obj.matrix_world


    for f in mesh.faces:
        if f.normal.normalized().z > threshold:
            f.select = True  # Optional: visually select in viewport
        else:
            f.select = False

    # Update the mesh
    bmesh.update_edit_mesh(obj.data, loop_triangles=False)

def recalculateNormals(obj):
    mesh = obj.data

    bm = bmesh.new()
    bm.from_mesh(mesh)

    # recalc normals outward
    bmesh.ops.recalc_face_normals(bm, faces=bm.faces)

    bm.to_mesh(mesh)
    bm.free()
    mesh.update()

def writeMetadata(obj, type = "MAP"):


    # 为生成的地图对象保存元数据信息
    if type == "MAP":
        obj["Object type"] = type  # 对象类型：地图
        obj["Addon"] = category     # 插件名称
        obj["Generation Duration"] = str(duration) + " seconds"  # 生成耗时
        obj["Shape"] = bpy.context.scene.tp3d.shape
        obj["Resolution"] = bpy.context.scene.tp3d.num_subdivisions
        obj["Elevation Scale"] = bpy.context.scene.tp3d.scaleElevation
        obj["objSize"] = bpy.context.scene.tp3d.objSize
        obj["pathThickness"] = round(bpy.context.scene.tp3d.pathThickness,2)
        obj["overwritePathElevation"] = bpy.context.scene.tp3d.overwritePathElevation
        obj["api"] = bpy.context.scene.tp3d.api
        obj["scalemode"] = bpy.context.scene.tp3d.scalemode
        obj["fixedElevationScale"] = bpy.context.scene.tp3d.fixedElevationScale
        obj["minThickness"] = bpy.context.scene.tp3d.minThickness
        obj["xTerrainOffset"] = bpy.context.scene.tp3d.xTerrainOffset
        obj["yTerrainOffset"] = bpy.context.scene.tp3d.yTerrainOffset
        obj["singleColorMode"] = bpy.context.scene.tp3d.singleColorMode
        obj["selfHosted"] = bpy.context.scene.tp3d.selfHosted
        obj["Horizontal Scale"] = round(bpy.context.scene.tp3d.sScaleHor,6)
        obj["Generate Water"] = bpy.context.scene.tp3d.col_wActive
        obj["MinWaterSize"] = bpy.context.scene.tp3d.col_wArea
        obj["Keep Non-Manifold"] = bpy.context.scene.tp3d.col_KeepManifold
        obj["Map Size in Km"] = round(bpy.context.scene.tp3d.sMapInKm,2)
        obj["Dovetail"] = False
        obj["MagnetHoles"] = False
        obj["AdditionalExtrusion"] = additionalExtrusion
        obj["lowestZ"] = lowestZ
        obj["highestZ"] = highestZ
        obj["dataset"] = bpy.context.scene.tp3d.dataset
        obj["name"] = bpy.context.scene.tp3d.name
        obj["pathScale"] = bpy.context.scene.tp3d.pathScale
        obj["scaleLon1"] = bpy.context.scene.tp3d.scaleLon1
        obj["scaleLat1"] = bpy.context.scene.tp3d.scaleLat1
        obj["scaleLon2"] = bpy.context.scene.tp3d.scaleLon2
        obj["scaleLat2"] = bpy.context.scene.tp3d.scaleLat2

        obj["shapeRotation"] = bpy.context.scene.tp3d.shapeRotation
        obj["pathVertices"] = bpy.context.scene.tp3d.o_verticesPath
        obj["mapVertices"] = bpy.context.scene.tp3d.o_verticesMap
        obj["mapScale"] = bpy.context.scene.tp3d.o_mapScale
        obj["centerx"] = bpy.context.scene.tp3d.o_centerx
        obj["centery"] = bpy.context.scene.tp3d.o_centery
        obj["sElevationOffset"] = bpy.context.scene.tp3d.sElevationOffset
        obj["sMapInKm"] = bpy.context.scene.tp3d.sMapInKm

        obj["col_wActive"] = bpy.context.scene.tp3d.col_wActive
        obj["col_wArea"] = bpy.context.scene.tp3d.col_wArea
        obj["col_fActive"] = bpy.context.scene.tp3d.col_fActive
        obj["col_fArea"] = bpy.context.scene.tp3d.col_fArea
        obj["col_cActive"] = bpy.context.scene.tp3d.col_cActive
        obj["col_cArea"] = bpy.context.scene.tp3d.col_cArea



    # 为路径对象保存元数据
    if type == "TRAIL":
        obj["Object type"] = type  # 对象类型：路径
        obj["Addon"] = category     # 插件名称
        obj["overwritePathElevation"] = bpy.context.scene.tp3d.overwritePathElevation
    
    # 为城市/水体/森林对象保存元数据
    if type == "CITY" or type == "WATER" or type == "FOREST":
        obj["Object type"] = type  # 对象类型：城市、水体或森林
        obj["Addon"] = category     # 插件名称
        obj["minThickness"] = bpy.context.scene.tp3d.minThickness  # 最小厚度

    # 为底板对象保存元数据
    if type == "PLATE":
        obj["Object type"] = type  # 对象类型：底板
        obj["Addon"] = category     # 插件名称
        obj["Shape"] = bpy.context.scene.tp3d.shape
        obj["textFont"] = bpy.context.scene.tp3d.textFont
        obj["textSize"] = bpy.context.scene.tp3d.textSize
        obj["overwriteLength"] = bpy.context.scene.tp3d.overwriteLength
        obj["overwriteHeight"] = bpy.context.scene.tp3d.overwriteHeight
        obj["overwriteTime"] = bpy.context.scene.tp3d.overwriteTime
        obj["outerBorderSize"] = bpy.context.scene.tp3d.outerBorderSize
        obj["shapeRotation"] = bpy.context.scene.tp3d.shapeRotation
        obj["name"] = bpy.context.scene.tp3d.name
        obj["plateThickness"] = bpy.context.scene.tp3d.plateThickness
        obj["plateInsertValue"] = bpy.context.scene.tp3d.plateInsertValue
        obj["textAngle"] = bpy.context.scene.tp3d.text_angle_preset
        obj["objSize"] = bpy.context.scene.tp3d.objSize * ((100 + bpy.context.scene.tp3d.outerBorderSize)/100)
    
    if type == "LINES":
        obj["Object type"] = type
        obj["cl_thickness"] = bpy.context.scene.tp3d.cl_thickness
        obj["cl_distance"] = bpy.context.scene.tp3d.cl_distance
        obj["cl_offset"] = bpy.context.scene.tp3d.cl_offset

    


def show_message_box(message, ic="ERROR", ti="ERROR"):
    """
    在Blender界面中显示消息弹窗
    
    参数：
        message (str): 要显示的消息内容
        ic (str): 图标类型，如"ERROR"、"INFO"、"WARNING"
        ti (str): 弹窗标题
    """
    #toggle_console()
    def draw(self, context):
        self.layout.label(text=message)
    print(message)  # 同时在控制台输出
    bpy.context.window_manager.popup_menu(draw, title=ti, icon=ic)

def toggle_console():
    """
    切换Blender控制台窗口的显示状态（仅Windows系统）
    
    用于调试和查看详细的生成过程信息
    """
    try:
        if platform.system() == "Windows":
            bpy.ops.wm.console_toggle()
    except Exception as e:
        print(f"无法切换控制台: {e}")
    
def runGeneration(type):
    """
    主生成函数：执行3D地图生成的完整流程
    
    这是插件的核心函数，整合了所有功能模块：
    1. 读取GPS轨迹文件
    2. 获取海拔数据
    3. 生成3D地形网格
    4. 创建路径曲线
    5. 应用材质和颜色
    6. 导出STL文件
    
    参数：
        type (int): 生成模式
            0 = 单个GPX文件
            1 = 批量处理多个GPX文件
            2 = 从中心点和半径创建地图
            3 = 从两个坐标点创建地图
            4 = 带路径的中心点地图
    """
    
    # ===== 检查Blender版本 =====
    # 插件需要Blender 4.5.0或更高版本才能正常运行
    required_version = (4, 5, 0)

    if bpy.app.version < required_version:
        show_message_box(f"此插件需要 Blender {required_version[0]}.{required_version[1]} 或更高版本。(您正在使用 {bpy.app.version_string})。")
        return
    
    start_time = time.time()

    toggle_console()
    
    for i in range(30):
        print(" ")
    print("------------------------------------------------")
    print("SCRIPT STARTED - DO NOT CLOSE THIS WINDOW")
    print("------------------------------------------------")
    print(" ")

    # Path to your GPX file
    global gpx_file_path
    gpx_file_path = bpy.context.scene.tp3d.get('file_path', None)
    global gpx_chain_path
    gpx_chain_path = bpy.context.scene.tp3d.get('chain_path', None)
    global exportPath
    exportPath = bpy.context.scene.tp3d.get('export_path', None)
    
    # 如果没有设置导出路径，使用GPX文件所在目录作为默认路径
    if not exportPath or exportPath == "":
        if gpx_file_path and gpx_file_path != "":
            import os
            # 获取GPX文件的目录
            gpx_dir = os.path.dirname(gpx_file_path)
            # 获取GPX文件名（不含扩展名）
            gpx_basename = os.path.splitext(os.path.basename(gpx_file_path))[0]
            # 设置导出路径为：GPX目录/GPX文件名（不含扩展名）
            exportPath = os.path.join(gpx_dir, gpx_basename)
            print(f"使用默认导出路径: {exportPath}")
    
    global shape
    shape = (bpy.context.scene.tp3d.shape)
    global name
    name = bpy.context.scene.tp3d.get('trailName', "")
    global size
    size =  bpy.context.scene.tp3d.get('objSize', 100)
    global num_subdivisions
    num_subdivisions = bpy.context.scene.tp3d.get('num_subdivisions', 8)
    global scaleElevation
    scaleElevation = bpy.context.scene.tp3d.get('scaleElevation', 2)
    global pathThickness
    pathThickness = bpy.context.scene.tp3d.get('pathThickness', 1.2)
    global scalemode
    scalemode = bpy.context.scene.tp3d.scalemode
    global pathScale
    pathScale = bpy.context.scene.tp3d.get('pathScale', 0.8)
    global scaleLon1
    scaleLon1 = bpy.context.scene.tp3d.get('scaleLon1', 0)
    global scaleLat1
    scaleLat1 = bpy.context.scene.tp3d.get('scaleLat1', 0)
    global scaleLon2
    scaleLon2 = bpy.context.scene.tp3d.get('scaleLon2', 0)
    global scaleLat2
    scaleLat2 = bpy.context.scene.tp3d.get('scaleLat2', 0)
    global shapeRotation
    shapeRotation = bpy.context.scene.tp3d.get('shapeRotation', 0)
    global overwritePathElevation
    overwritePathElevation = bpy.context.scene.tp3d.get('overwritePathElevation', True)
    global api
    api = bpy.context.scene.tp3d.get('api',2)
    global dataset
    #dataset_int = bpy.context.scene.tp3d.get("dataset",1)
    dataset = bpy.context.scene.tp3d.dataset
    global selfHosted
    selfHosted = bpy.context.scene.tp3d.get("selfHosted","")
    global fixedElevationScale
    fixedElevationScale = bpy.context.scene.tp3d.get('fixedElevationScale', False)
    global minThickness
    minThickness = bpy.context.scene.tp3d.get("minThickness",7)
    global xTerrainOffset
    xTerrainOffset = bpy.context.scene.tp3d.get("xTerrainOffset",0)
    global yTerrainOffset
    yTerrainOffset = bpy.context.scene.tp3d.get("yTerrainOffset",0)
    global singleColorMode
    singleColorMode = bpy.context.scene.tp3d.get("singleColorMode",True)
    global disableCache
    disableCache = bpy.context.scene.tp3d.get("disableCache",0)
    global cacheSize
    cacheSize = bpy.context.scene.tp3d.get("ccacheSize",50000)

    #OTHER VARIABLES FOR TEXT BASED SHAPES
    #Add input fields
    global textFont
    textFont = bpy.context.scene.tp3d.get("textFont","")
    global textSize
    textSize = bpy.context.scene.tp3d.get("textSize",10)
    global overwriteLength
    overwriteLength = bpy.context.scene.tp3d.get("overwriteLength","")
    global overwriteHeight
    overwriteHeight = bpy.context.scene.tp3d.get("overwriteHeight","")
    global overwriteTime
    overwriteTime = bpy.context.scene.tp3d.get("overwriteTime","")
    global outerBorderSize
    outerBorderSize = bpy.context.scene.tp3d.get("outerBorderSize",20)
    global text_angle_preset
    text_angle_preset = int(bpy.context.scene.tp3d.text_angle_preset)
    global plateThickness
    plateThickness = bpy.context.scene.tp3d.get("plateThickness",5)

    col_wActive = (bpy.context.scene.tp3d.col_wActive)
    col_fActive = (bpy.context.scene.tp3d.col_fActive)
    col_cActive = (bpy.context.scene.tp3d.col_cActive)

    global jMapLat
    jMapLat = bpy.context.scene.tp3d.get("jMapLat",49)
    global jMapLon
    jMapLon = bpy.context.scene.tp3d.get("jMapLon",9)
    global jMapRadius
    jMapRadius = bpy.context.scene.tp3d.get("jMapRadius",50)

    global jMapLat1
    jMapLat1 = bpy.context.scene.tp3d.get("jMapLat1",48)
    global jMapLon1
    jMapLon1 = bpy.context.scene.tp3d.get("jMapLon1",8)
    global jMapLat2
    jMapLat2 = bpy.context.scene.tp3d.get("jMapLat2",49)
    global jMapLon2
    jMapLon2 = bpy.context.scene.tp3d.get("jMapLon2",9)

    


    global opentopoAdress
    opentopoAdress = "https://api.opentopodata.org/v1/"
    if selfHosted != "" and selfHosted != None and api == 1:
        opentopoAdress = selfHosted
        print(f"!!using {opentopoAdress} instead of Opentopodata!!")
    
    

    
    #CHECK FOR VALID INPUTS
    if type == 0 or type == 4:
        
        if not gpx_file_path or gpx_file_path == "":
            show_message_box("文件路径为空！请选择一个有效的文件。")
            toggle_console()
            return
        import os
        if not os.path.isfile(gpx_file_path):
            show_message_box(f"无效的文件路径：{gpx_file_path}。请选择一个有效的文件。")
            toggle_console()
            return
        gpx_file_path = bpy.path.abspath(gpx_file_path)

        file_extension = os.path.splitext(gpx_file_path)[1].lower()
        if file_extension != '.gpx' and file_extension != ".igc":
            show_message_box(f"无效的文件格式。请使用 .GPX 或 .IGC 文件")
            toggle_console()
            return
    
    if type == 1:
        if not gpx_chain_path or gpx_chain_path == "":
            show_message_box("链式路径为空！请选择一个有效的文件夹。")
            toggle_console()
            return
        gpx_chain_path = bpy.path.abspath(gpx_chain_path)
    if type == 2:
        #check if inputs are valid
        pass
    if type == 3:
        #check if inputs are valid
        pass
    if exportPath == None:
        show_message_box("导出路径不能为空")
        toggle_console()
        return
    
    exportPath = bpy.path.abspath(exportPath)

    if not exportPath or exportPath == "":
        show_message_box("导出路径为空！请选择一个有效的文件夹。")
        toggle_console()
        return
    if not os.path.isdir(exportPath):
        show_message_box(f"无效的导出目录：{exportPath}。请选择一个有效的目录。")
        toggle_console()
        return


    # 如果用户未指定字体路径，自动查找系统中文字体
    if textFont == "":
        textFont = get_chinese_font()
        
        # 如果没有找到中文字体，使用系统默认英文字体作为备用
        if textFont == "":
            if platform.system() == "Windows":
                textFont = "C:/WINDOWS/FONTS/ariblk.ttf"  # Windows默认粗体
            elif platform.system() == "Darwin":
                textFont = "/System/Library/Fonts/Supplemental/Arial Black.ttf"  # macOS默认粗体
            else:
                textFont = ""  # Linux使用Blender内置字体
                #show_message_box(f"请在形状设置选项卡中选择字体。")
                #toggle_console()
                #return
        
    
    if name == "":
        if type == 0 or type == 4:
            name_with_ext = os.path.basename(gpx_file_path)
            name = os.path.splitext(name_with_ext)[0]
        if type == 1:
            name_with_ext = os.path.basename(os.path.normpath(gpx_chain_path))
            name = os.path.splitext(name_with_ext)[0]
        if type == 2 or type == 3:
            name = "Terrain"
        
    #GENERATE COLORS IF THEY ARENT THERE YET
    setupColors()
        
    #CONSOLE MESSAGES
    if disableCache == 1:
        print("Cache Disabled (in Advanced Settings)")
    if overwritePathElevation == True and singleColorMode == False:
        print("Overwrite Path Elevation enabled: Path Elevation will be overwritten")
    if type == 0 or type == 1 or type == 4:
        if xTerrainOffset > 0:
            print(f"Map will be moved in X by {xTerrainOffset} (Advanced Settings -> Map -> xTerrainOffset)")
        if yTerrainOffset > 0:
            print(f"Map will be moved in Y by {yTerrainOffset} (Advanced Settings -> Map -> yTerrainOffset)")
    if col_wActive == 1 or col_fActive == 1 or col_cActive == 1:
        print(f"Auto Colors is activated -> Still in Testphase. results may not be perfect")

    
    if singleColorMode == True:
        overwritePathElevation = False
        print("Overwrite path Elevation was disabled as its not needed in Single Color mode")

    #STARTSETTINGS
    #Leave edit mode      
    if bpy.context.object and bpy.context.object.mode == 'EDIT':
        bpy.ops.object.mode_set(mode='OBJECT')

    # Disable Auto Merge Vertices
    bpy.context.scene.tool_settings.use_mesh_automerge = False
        
    coordinates = []
    coordinates2 = []
    tempcoordinates = []
    separate_paths = []
    # Load GPX data        
    #try:
    if 1 == 1:
        if type == 0:
            
            separate_paths = read_gpx_file()
        if type == 1:
            separate_paths = read_gpx_directory(gpx_chain_path)
        if type == 2 or type == 4:
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"e")
            separate_paths.append([(nlat,nlon,0,0)])
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"s")
            separate_paths.append([(nlat,nlon,0,0)])
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"w")
            separate_paths.append([(nlat,nlon,0,0)])
            nlat,nlon = move_coordinates(jMapLat,jMapLon,jMapRadius,"n")
            separate_paths.append([(nlat,nlon,0,0)])

            if type == 4:
                tempcoordinates = read_gpx_file()
                coordinates2 = [item for sublist in tempcoordinates for item in sublist]

        if type == 3:
            separate_paths.append([(jMapLat1,jMapLon1,0,0)])
            separate_paths.append([(jMapLat2,jMapLon2,0,0)])
    #except Exception as e:
    else:
        show_message_box(f"读取GPX文件时出错。类型：{type}")
        return
    coordinates = [item for sublist in separate_paths for item in sublist]
    #coordinates = separate_paths

    #print(f"separaite paits: {len(separate_paths)}")
    


    
    #Calculating some Stats about the path
    global total_length
    global total_elevation
    global total_time
    total_length = 0
    total_elevation = 0
    total_time = 0
    if type == 0 or type == 1:
        total_length = calculate_total_length(coordinates)
        total_elevation = calculate_total_elevation(coordinates)
        total_time = calculate_total_time(coordinates)


    hours = int(total_time)
    minutes = int((total_time - hours) * 60)
    global time_str
    time_str = f"{hours}h {minutes}m"

    while len(coordinates) < 300 and len(coordinates) > 1 and type != 2:
        i = 0
        while i < len(coordinates) - 1:
            p1 = coordinates[i]
            p2 = coordinates[i + 1]

            # Calculate midpoint (only for x, y, z)
            midpoint = (
                (p1[0] + p2[0]) / 2,
                (p1[1] + p2[1]) / 2,
                (p1[2] + p2[2]) / 2,
                (p1[3])  # Optional: interpolate time too
            )

            # Insert midpoint before p2
            coordinates.insert(i + 1, midpoint)

            # Skip over the new point and the original next point
            i += 2
    

    #CALCULATE biggest distance so you can calculate the value for the smoothing
    min_x = max(point[0] for point in coordinates)
    max_x = max(point[0] for point in coordinates)
    min_y = min(point[1] for point in coordinates)
    max_y = max(point[1] for point in coordinates)
    p1 = convert_to_blender_coordinates(min_x, min_y, 0,"")
    p2 = convert_to_blender_coordinates(max_x,max_y, 0,"")

    distance = math.sqrt((p2[0] - p1[0]) ** 2 + (p2[1] - p1[1]) ** 2)


    #Überschreiben der elevation werte der GXP mit den Elevation werte der gleichen API mit der das Terrain erstellt wird
    '''
    PREVIOUS LOGIC TO OVERWRITE PATH. REPLACE BY RAYCASTING CURVE POINTS ONTO MESH
    if overwritePathElevation == True:
        print(" ")
        print(" ")
        print("------------------------------------------------")
        print("FETCHING ELEVATION DATA FOR THE PATH")
        print("------------------------------------------------")
        print(" ")
        try:
            if type == 0 and len(separate_paths) == 1:
                print("First")
                if api == 1:
                    coordinates = get_elevation_path_openElevation(coordinates)
                else:
                    coordinates = get_elevation_path_openTopoData(coordinates)
            if type == 1 or len(separate_paths) > 1:
                print("Second")
                if api == 1:
                    separate_paths = [get_elevation_path_openElevation(path) for path in separate_paths]
                else:
                    print(separate_paths)
                    sp = []
                    sp.extend(get_elevation_path_openTopoData(path) for path in separate_paths)
                    separate_paths = sp
                    print("-----")
                    print(separate_paths)
                
                coordinates = [item for sublist in separate_paths for item in sublist]
            if type == 4:
                if api == 1:
                    tempcoordinates = get_elevation_path_openElevation(coordinates2)
                else:
                    tempcoordinates = get_elevation_path_openTopoData(coordinates2)
        except Exception as e:
            show_message_box("尝试覆盖路径时API响应错误。这种情况偶尔会发生")
            return
        '''
    
    #CALCULATE SCALE 
    global scaleHor

    scalecoords = coordinates
    if scalemode == "COORDINATES" and (type == 0 or type == 1):
        c2 = ((scaleLon1,scaleLat1),(scaleLon2,scaleLat2))
        scalecoords = c2


    scaleHor = calculate_scale(size, scalecoords)
    print(f"scaleHor: {scaleHor}")

    bpy.context.scene.tp3d["sScaleHor"] = scaleHor
    

    

    # Convert coordinates to Blender format and create a curve
    #print("Converting Coordinates to Blender format coordinates for X and Y coordsd")
    blender_coords = [convert_to_blender_coordinates(lat, lon, ele,timestamp) for lat, lon, ele, timestamp in coordinates]
    
    if type == 1 or len(separate_paths) > 1:
        blender_coords_separate = [
            [convert_to_blender_coordinates(lat, lon, ele, timestamp) for lat, lon, ele, timestamp in path]
            for path in separate_paths
            ]

  
    
    #CALCULATE CENTER
    min_x = min(point[0] for point in blender_coords)
    max_x = max(point[0] for point in blender_coords)
    min_y = min(point[1] for point in blender_coords)
    max_y = max(point[1] for point in blender_coords)
    
    global centerx
    global centery
    centerx = (max_x-min_x)/2 + min_x
    centery = (max_y-min_y)/2 + min_y

    #if type == 2:
    #centerx,centery,z = convert_to_blender_coordinates(jMapLat,jMapLon,0,0)


    bpy.context.scene.tp3d["o_centerx"] = centerx
    bpy.context.scene.tp3d["o_centery"] = centery

    #print(f"CenterX: {centerx}, CenterY: {centery}")
    
    #DELETE OBJECTS THAT SIT AT THE CENTER TO PREVENT OVERLAPPING
    target_location_2d = Vector((centerx,centery))
    for obs in bpy.data.objects:
        obj_location_2d = Vector((obs.location.x, obs.location.y))
        if (obj_location_2d - target_location_2d).length <= 0.1:
            bpy.data.objects.remove(obs, do_unlink = True)
            print("deleted overlapping object (Previous generated objects)")

    bpy.ops.object.select_all(action='DESELECT')

    global MapObject
    # CREATE SHAPES
    #print("Creating MapObject")
    if shape == "HEXAGON": #hexagon
        MapObject = create_hexagon(size/2)
    elif shape == "SQUARE": #rectangle
        MapObject = create_rectangle(size,size)
    elif shape == "HEXAGON INNER TEXT": #Hexagon with inner text
        MapObject = create_hexagon(size/2)
    elif shape == "HEXAGON OUTER TEXT": #Hexagon with outer text
        MapObject = create_hexagon(size/2)
    elif shape == "HEXAGON FRONT TEXT": #Hexagon with front text
        MapObject = create_hexagon(size/2)
    elif shape == "CIRCLE": #circle
        MapObject = create_circle(size/2)

    else:
        MapObject = create_hexagon(size/2)
    
    recalculateNormals(MapObject)

    
    #SHAPE ROTATION
    MapObject.rotation_euler[2] += shapeRotation * (3.14159265 / 180)
    MapObject.select_set(True)
    bpy.context.view_layer.objects.active = MapObject
    bpy.ops.object.transform_apply(location = False, rotation=True, scale = False)

    targetx = centerx + xTerrainOffset
    targety = centery + yTerrainOffset
    #print(f"targetx: {targetx}, targety: {targety}")
    if scalemode == "COORDINATES" and type == 1:
        midLat, midLon = midpoint_spherical(scaleLat1,scaleLon1,scaleLat2,scaleLon2)
        targetx, targety, el = convert_to_blender_coordinates(midLat,midLon,0,0)
    #print(f"targetx: {targetx}, targety: {targety}")

    transform_MapObject(MapObject, targetx, targety)

    if type == 4:
        coordinates = coordinates2
    

    #fetch and apply the elevation
    print("------------------------------------------------")
    print("FETCHING ELEVATION DATA FOR THE MAP")
    print("------------------------------------------------")
    
    global autoScale
    bpy.ops.object.transform_apply(location = False, rotation = True, scale = True)
    tileVerts, diff = get_tile_elevation(MapObject)
    
    # 调试信息：显示网格顶点数和海拔数据数量
    mesh_vert_count = len(MapObject.data.vertices)
    print(f"调试: 网格顶点数={mesh_vert_count}, 海拔数据数={len(tileVerts)}")
    if mesh_vert_count != len(tileVerts):
        print(f"⚠️  警告: 数量不匹配! 差异={mesh_vert_count - len(tileVerts)}")

    if len(tileVerts) < 2000:
            show_message_box(f"网格只有{len(tileVerts)}个点。增加细分数量以提高分辨率", "INFO", "信息")
    
    if fixedElevationScale == True:
        if diff > 0:
            autoScale = 10/(diff/1000)
        else:
            autoScale = 10
    else:
        autoScale = scaleHor
    
    bpy.context.scene.tp3d["sAutoScale"] = autoScale



    if fixedElevationScale == False:
        if diff == 0:
            pass
            show_message_box("地形似乎非常平坦。该区域可能没有海拔数据。请尝试不同的API或数据集", "INFO", "信息")
        elif (diff/1000) * autoScale * scaleElevation < 2 :
            show_message_box("地形似乎较为平坦。增加海拔缩放可能会有所帮助", "INFO", "信息")

    
    #RECALCULATE THE COORDS WITH AUTOSCALE APPLIED
    blender_coords = [convert_to_blender_coordinates(lat, lon, ele,timestamp) for lat, lon, ele, timestamp in coordinates]

    blender_coords = simplify_curve(blender_coords, .12)

    #PREVENT CLIPPING OF IDENTICAL COORDINATES
    blender_coords = separate_duplicate_xy(blender_coords, 0.05) 
    
    if (type == 1 or len(separate_paths) > 1) and type != 4:
        blender_coords_separate = [
            [convert_to_blender_coordinates(lat, lon, ele, timestamp) for lat, lon, ele, timestamp in path]
            for path in separate_paths
            ]
    
    #calculate real Scale
    tdist = 0
    lat1 = coordinates[0][0]
    lon1 = coordinates[0][1]
    lat2 = coordinates[-1][0]
    lon2 = coordinates[-1][1]
    tdist = haversine(lat1,lon1 ,lat2 , lon2)
    #print(f"lat1: {lat1} | lon1: {lon1} ||| lat2: {lat2} | lon2: {lon2}")
    #print(f"tdist:{tdist}")
    mscale = (tdist/size) * 1000000
    #print(f"scale: {mscale}")
    bpy.context.scene.tp3d["o_mapScale"] = f"{mscale:.0f}"

    #------------------------------------------------------------------------------------------------------------------------
    #CREATE THE PATH
    #print("Creating Curve")
    global curveObj
    curveObj = None
    try:
        if type == 0 or len(blender_coords_separate) == 1 or type == 4:
            #print(blender_coords)
            create_curve_from_coordinates(blender_coords)
            curveObj = bpy.context.view_layer.objects.active
        elif (type == 1 or len(blender_coords_separate) > 1) and type != 4:
            for crds in blender_coords_separate:
                create_curve_from_coordinates(crds)
                
                bpy.ops.object.join()
                curveObj = bpy.context.view_layer.objects.active
    except Exception as e:
        show_message_box("创建曲线时API响应错误。如果持续发生请联系开发者")
        return
    
    
    bpy.ops.object.select_all(action='DESELECT')
    
    
    #APPLY TERRAIN ELEVATION
    mesh = MapObject.data

    global lowestZ
    global highestZ  
    lowestZ = 1000
    highestZ = 0
    
    # 添加边界检查：确保 tileVerts 和 mesh.vertices 数量匹配
    if len(tileVerts) != len(mesh.vertices):
        print(f"警告: tileVerts 长度 ({len(tileVerts)}) 与顶点数量 ({len(mesh.vertices)}) 不匹配!")
        show_message_box(f"海拔数据不匹配！预期{len(mesh.vertices)}个点但获得{len(tileVerts)}个。请尝试降低分辨率或重新生成。", "ERROR", "错误")
        # 使用安全的索引访问
        for i, vert in enumerate(mesh.vertices):
            if i < len(tileVerts):
                vert.co.z = (tileVerts[i] - elevationOffset)/1000 * scaleElevation * autoScale
            else:
                # 超出范围的顶点使用最后一个已知海拔值
                vert.co.z = (tileVerts[-1] - elevationOffset)/1000 * scaleElevation * autoScale
            if vert.co.z < lowestZ:
                lowestZ = vert.co.z
            if vert.co.z > highestZ:
                highestZ = vert.co.z
    else:
        # 正常情况：长度匹配
        for i, vert in enumerate(mesh.vertices):
            vert.co.z = (tileVerts[i] - elevationOffset)/1000 * scaleElevation * autoScale
            if vert.co.z < lowestZ:
                lowestZ = vert.co.z
            if vert.co.z > highestZ:
                highestZ = vert.co.z
            
    global additionalExtrusion
    additionalExtrusion = lowestZ

    bpy.context.scene.tp3d["sAdditionalExtrusion"] = additionalExtrusion
    
    # 修复网格中的异常点
    print("正在修复网格异常点...")
    fix_mesh_anomalies(MapObject, threshold=0.1)
    
    #Raycast the curve points onto the Mesh surface
    if overwritePathElevation == True:
        RaycastCurveToMesh(curveObj, MapObject)
    
    
    # Extrude hexagon to z=0 and scale bottom face
    #bpy.context.scene.tool_settings.transform_pivot_point = 'CURSOR'
    bpy.context.view_layer.objects.active = MapObject
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.mesh.extrude_region_move()
    bpy.ops.mesh.dissolve_faces() #Merge the bottom faces to a single face
    bpy.ops.transform.translate(value=(0, 0, -1))#bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.object.mode_set(mode='OBJECT')

    global obj
    obj = bpy.context.object


    # Get the mesh data
    mesh = obj.data
    # Get selected faces
    selected_faces = [face for face in mesh.polygons if face.select]
    
    
    if selected_faces:
        for face in selected_faces:
            for vert_idx in face.vertices:
                vert = mesh.vertices[vert_idx]
                vert.co.z = additionalExtrusion - minThickness
    else:
        print("No face selected.")
    
    #CHANGE OBJECT ORIGIN
    bpy.context.view_layer.objects.active = MapObject
    bpy.ops.object.mode_set(mode='EDIT')
    bpy.ops.mesh.select_all(action='SELECT')
    bpy.ops.transform.translate(value=(0, 0, -additionalExtrusion+minThickness))#bpy.ops.mesh.select_all(action='DESELECT')
    bpy.ops.object.mode_set(mode='OBJECT')

    if curveObj:
        bpy.context.view_layer.objects.active = curveObj
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.curve.select_all(action='SELECT')
        bpy.ops.transform.translate(value=(0, 0, -additionalExtrusion+minThickness))#bpy.ops.mesh.select_all(action='DESELECT')
        bpy.ops.object.mode_set(mode='OBJECT')

    
    
    #sets 3D cursor to origin of tile
    location = obj.location
    bpy.context.scene.cursor.location = location
    if curveObj:
        curveObj.select_set(True)
        bpy.ops.object.origin_set(type="ORIGIN_CURSOR")
    
    #Set tile as parent to path
    #curveObj.parent = obj
    #curveObj.matrix_parent_inverse = obj.matrix_world.inverted()
    
    recalculateNormals(obj)


    #ADDITIONAL SHAPE STUFF
    if shape == "HEXAGON INNER TEXT":
        HexagonInnerText()
    if shape == "HEXAGON OUTER TEXT":
        HexagonOuterText()
        obj.location.z += plateThickness
        if curveObj:
            curveObj.location.z += plateThickness
    if shape == "OCTAGON OUTER TEXT":
        OctagonOuterText()
        obj.location.z += plateThickness
        if curveObj:
            curveObj.location.z += plateThickness
    if shape == "HEXAGON FRONT TEXT":
        HexagonFrontText()
        obj.location.z += plateThickness
        if curveObj:
            curveObj.location.z += plateThickness
    else:
        pass
        #BottomText()


    #PLATESHAPE INSERT - 必须在单色模式之前执行，以避免底板包含路径信息
    dist = bpy.context.scene.tp3d.plateInsertValue
    if dist > 0:
        if shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
            plate = bpy.data.objects.get(name + "_Plate")
            plateInsert(plate, obj)
            text = bpy.data.objects.get(name + "_Text")
            text.location.z += dist


    #SINGLE COLOR MODE - 在底板生成之后执行，这样路径合并到地图时不会影响底板
    if singleColorMode == 1 and curveObj:
        single_color_mode(curveObj,obj.name)
    
    
    #ADD FLAGS AT PATH ENDPOINTS - 在路径起点和终点添加旗帜标记
    addFlags = bpy.context.scene.tp3d.get("addFlags", False)
    if addFlags and curveObj:
        print(" ")
        print("------------------------------------------------")
        print("添加旗帜标记")
        print("------------------------------------------------")
        
        flagHeight = bpy.context.scene.tp3d.get("flagHeight", 5.0)
        flagWidth = bpy.context.scene.tp3d.get("flagWidth", 3.0)
        
        try:
            # 查找路径的起点和终点
            start_point, end_point = find_path_endpoints(curveObj)
            
            if start_point and end_point:
                # 在起点创建起点旗帜（绿色）
                start_flag = create_flag(name + "_StartFlag", start_point, "START", flagHeight, flagWidth)
                if start_flag:
                    print(f"✓ 起点旗帜已创建于路径起点: ({start_point[0]:.2f}, {start_point[1]:.2f}, {start_point[2]:.2f})")
                    # 导出STL
                    export_to_STL(start_flag)
                
                # 在终点创建终点旗帜（红色）
                finish_flag = create_flag(name + "_FinishFlag", end_point, "FINISH", flagHeight, flagWidth)
                if finish_flag:
                    print(f"✓ 终点旗帜已创建于路径终点: ({end_point[0]:.2f}, {end_point[1]:.2f}, {end_point[2]:.2f})")
                    # 导出STL
                    export_to_STL(finish_flag)
                
                print("✓ 旗帜标记添加完成")
            else:
                print("⚠️  警告: 无法找到路径端点")
                
        except Exception as e:
            print(f"⚠️  创建旗帜时出错: {str(e)}")
            import traceback
            traceback.print_exc()
    

    #ZOOM TO OBJECT
    zoom_camera_to_selected(obj)
    
    bpy.ops.object.select_all(action='DESELECT')


    #ADD COLORS TO OBJECTS
    mat = bpy.data.materials.get("BASE")
    obj.data.materials.clear()
    obj.data.materials.append(mat)

    if curveObj:
        mat = bpy.data.materials.get("TRAIL")
        curveObj.data.materials.clear()
        curveObj.data.materials.append(mat)

    #MATERIAL PREVIEW MODE
    for area in bpy.context.screen.areas:
        if area.type == 'VIEW_3D':  # make sure it's a 3D Viewport
            for space in area.spaces:
                if space.type == 'VIEW_3D':
                    space.shading.type = 'MATERIAL'  # switch shading
    
    #WATER MESH
    if col_wActive == 1:
        coloring_main(obj, "WATER")
    if col_fActive == 1:
        coloring_main(obj, "FOREST")
    if col_cActive == 1:
        coloring_main(obj, "CITY")
    
    #EXPORT STL
    if curveObj:
        export_to_STL(curveObj)
    export_to_STL(obj)
    
    if shape == "HEXAGON INNER TEXT" or shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
        tobj = textobj
        mat = bpy.data.materials.get("WHITE")
        if shape == "HEXAGON INNER TEXT":
            mat = bpy.data.materials.get("TRAIL")
        tobj.data.materials.clear()
        tobj.data.materials.append(mat)
        export_to_STL(tobj)
    if shape == "HEXAGON OUTER TEXT" or shape == "OCTAGON OUTER TEXT" or shape == "HEXAGON FRONT TEXT":
        plobj = plateobj
        mat = bpy.data.materials.get("BLACK")
        plobj.data.materials.clear()
        plobj.data.materials.append(mat)
        writeMetadata(plobj, type = "PLATE")
        export_to_STL(plobj)
    
    
    end_time = time.time()
    duration = end_time - start_time
    
    bpy.context.scene.tp3d["o_time"] = f"Script ran for {duration:.0f} seconds"


    #STORE VALUES IN MAP
    writeMetadata(obj)

    if type != 2:
        writeMetadata(curveObj,"TRAIL")
    
    #API Counter updaten
    count_openTopoData, last_date_openTopoData, count_openElevation, last_date_openElevation  = load_counter()
    if count_openTopoData < 1000:
        bpy.context.scene.tp3d["o_apiCounter_OpenTopoData"] = f"API Limit: {count_openTopoData:.0f}/1000 daily"
    else:
        bpy.context.scene.tp3d["o_apiCounter_OpenTopoData"] = f"API Limit: {count_openTopoData:.0f}/1000 (daily limit reached. might cause problems)"
    
    if count_openElevation < 1000:
        bpy.context.scene.tp3d["o_apiCounter_OpenElevation"] = f"API Limit: {count_openElevation:.0f}/1000 Monthly"
    else:
        bpy.context.scene.tp3d["o_apiCounter_OpenElevation"] = f"API Limit: {count_openElevation:.0f}/1000 (Monthly limit reached. might cause problems)"
        
    
        
    print(f"Finished")

    toggle_console()